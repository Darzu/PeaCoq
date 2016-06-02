"use strict";

//TODO:
// - add priorities to async requests
//   - and/or: wait until proof process is idle before trying proofs

//Algorithm:
//  after proof cursor changes:
//    check validity of in-progress proofs
//    create new attempts for goals not in progress

function Brute() {
  //console.log("Brute hook: [constr]");

  //in-progress synthesis attempts
  this.curAttempts = []
  this.curGoals = []
  this.curUnfocused = []
  this.curContextHashes = []
}

window.brute = new Brute();

$(document).ready(function() {
  //console.log("Brute hook: [doc. ready]");
});

//Copy-pasta: http://stackoverflow.com/questions/7616461/generate-a-hash-from-string-in-javascript-jquery
if (!"".hashCode) {
  String.prototype.hashCode = function() {
    var hash = 0, i, chr, len;
    if (this.length === 0) return hash;
    for (i = 0, len = this.length; i < len; i++) {
      chr   = this.charCodeAt(i);
      hash  = ((hash << 5) - hash) + chr;
      hash |= 0; // Convert to 32bit integer
    }
    return hash;
  };
}

function assert(cond, msg) {
  if (!cond) {
    if (msg)
      console.error(msg)
    debugger;
  }
}

function getHyps(goal) {
  return _.map(goal.gHyps, h => extractHypothesis(h))
}
function getHypStrs(goal) {
  return _.map(getHyps(goal), h => PT.showHypothesisText(h))
}
function getGoalInfo(goal) {
  return extractGoal(goal.gGoal);
}
function getGoalStr(goal) {
  return showTermText(getGoalInfo(goal))
}
function getContextStr(goal) {
  return getHypStrs(goal).join("\n") 
    + "\n--------------------\n"
    + getGoalStr(goal)
}
function getContextHash(goal) {
  return getContextStr(goal).hashCode();
}

function BruteAttempt(goal, goalNum, contextHash) {
  //TODO: can we get away with tracking less state?
  this.goal = goal;
  this.goalNum = goalNum;
  if (!contextHash)
    contextHash = getContextHash(goal)
  this.contextHash = contextHash;
  this.isValid = true;
  this.solution = null;
  this.depth = 0;
  this.maxDepth = 0;
  this.additiveTacs = [];
}
BruteAttempt.prototype.updateValidity = function() {
  if (!this.isValid)
    return;
  var goalIdx = this.goalNum - 1;
  var curHash = brute.curContextHashes[goalIdx];
  var sameHash = curHash === this.contextHash;
  //See if the goal changed numbers
  if (!sameHash) {
    var newGoalNum = _.indexOf(brute.curContextHashes, this.contextHash) + 1;
    if (newGoalNum > 0 && !_.any(brute.curAttempts, a => a.goalNum === newGoalNum)) {
      this.changeGoalNum(newGoalNum)
    } else {
      this.isValid = false
      if (this.hasSolution()) {
        brute.onProofInvalidated(this);
      }
    }
  }
}
BruteAttempt.prototype.changeGoalNum = function(newGoalNum) {
  this.goalNum = newGoalNum;
  this.run();
}
BruteAttempt.prototype.hasSolution = function() {
  return !!this.solution;
}
BruteAttempt.prototype.run = function() {
  if (this.depth % 2 === 0) {
    this.trySolve();
  } else {
    this.tryAddTac();
  }
}
BruteAttempt.prototype.trySolve = function() {
  var self = this;
  var onQuerySuccess = (tactic, query, response) => {
    self.solution = query;
    brute.onProofFound(self);
  }
  var getTactics = () => {
    return getSolveTactics(this.goal)
  }
  var mkQuery = (t) => {
    return t;
  }
  var shouldStopEarly = () => {
    return false;
  }
  self.tryAtDepth(getTactics, onQuerySuccess, mkQuery, shouldStopEarly);
}
BruteAttempt.prototype.tryAddTac = function() {
  var self = this;
  var found = false;
  var onQuerySuccess = (tactic, query, response) => {
    self.additiveTacs.push(tactic);
    found = true;
  }
  var getTactics = () => {
    return getAdditiveTactics(this.goal);
  }
  var mkQuery = (t) => {
    return t + "; []";
  }
  var shouldStopEarly = () => {
    return found;
  }
  self.tryAtDepth(getTactics, onQuerySuccess, mkQuery, shouldStopEarly);
}
BruteAttempt.prototype.tryAtDepth = function(getTactics, onQuerySuccess, mkQuery, shouldStopEarly) {
  var self = this;
  var queryGoalNum = this.goalNum;
  var queryDepth = this.depth;
  var anyCancelled = false;
  var _isQueryValid = true;

  var isDepthAttemptValid = () => {
    return self.isValid 
        && self.goalNum === queryGoalNum 
        && self.depth === queryDepth
        && !self.hasSolution();
  }
  var tryGoDeeper = () => {
    if (self.depth < self.maxDepth) {
      self.depth++;
      self.run();
    } else {
      //console.log("Giving up at depth: "+self.depth);
    }
  }
  var onAllQueriesFinished = () => {
    if (isDepthAttemptValid()) {
      tryGoDeeper()
    } else {
      //query failed      
    }
  }
  var isQueryValid = () => {
    if (!_isQueryValid)
      return false;
    
    //Recheck
    _isQueryValid = isDepthAttemptValid() && !shouldStopEarly()

    return _isQueryValid;
  }
  var onQueryCancelled = () => {
    if (isDepthAttemptValid()) {
      tryGoDeeper();
    }
  }
  var shouldCancelQuery = () => {
    var res = !isQueryValid();
    if (res && !anyCancelled) {
      anyCancelled = true;
      onQueryCancelled();
    }
    return res;
  }

  var promises = []

  var tacs = getTactics();
  _.forEach(tacs, tac => {
    var queryPrefix = queryGoalNum > 1 ? queryGoalNum + ": " : "";
    var prevQuery = _.map(this.additiveTacs, t => t + ". ").join("");
    var query = queryPrefix + prevQuery + mkQuery(tac) + ".";

    var promise = asyncQueryAndUndo(query, shouldCancelQuery)
      .then(delayPromise(0))
      .then(function(response) {
        if (isGood(response)) {
          if (isQueryValid()) {  
            onQuerySuccess(tac, query, response);
          }
        }
      })
      .catch(outputError);

    promises.push(promise)
  })  

  Promise.all(promises)
    .then(function() {
      onAllQueriesFinished();
    });
}

// BruteAttempt.prototype.tryAddTac = function() {
//   var self = this;
//   var queryGoalNum = this.goalNum;
//   var queryDepth = this.depth;

//   var isQueryValid = () => {
//     return self.isValid 
//       && self.goalNum === queryGoalNum 
//       && self.depth === queryDepth
//       && !self.hasSolution()
//   }

//   var promises = []

//   var tacs = getAdditiveTactics(self.goal);
//   _.forEach(tacs, tac => {
//     var queryPrefix = queryGoalNum > 1 ? queryGoalNum + ": " : "";
//     var prevQuery = _.map(this.additiveTacs, t => t + ". ").join("");
//     var query = queryPrefix + prevQuery + tac + ".";

//     var promise = asyncQueryAndUndo(query, () => !isQueryValid)
//       .then(delayPromise(0))
//       .then(function(response) {
//           if (isGood(response)) {
//             if (isQueryValid()) {      
//               self.solution = query;
//               brute.onProofFound(self);
//             }
//           }
//       })
//       .catch(outputError);

//     promises.push(promise)
//   })  

//   Promise.all(promises)
//     .then(function() {
//       if (isQueryValid()) {
//         console.log("Failed at depth: "+self.depth);
//       } else {
//         //what to do?
//       }
//     });
// }

Brute.prototype.update = function(response) {
  var self = this;

  if (!isGood(response))
    return; //TODO handle bad states

  var focused = response.rGoals.focused;
  var unfocused = _.flatten(response.rGoals.unfocused);
  var goals = focused; //TODO: try solving unfocused goals too

  this.curGoals = goals  
  this.curUnfocused = unfocused

  //Recompute context hashes
  this.curContextHashes = _.map(goals, getContextHash);

  //Update validity of current atttempts
  _.forEach(this.curAttempts, a => a.updateValidity());

  if (goals.length === 0)
    return;

  //Keep valid attempts
  this.curAttempts = _.filter(this.curAttempts, a => a.isValid);

  //Start new attempts
  for (var goalIdx = 0; goalIdx < goals.length; goalIdx++) {
    var goalNum = goalIdx + 1;
    var hasAttempt = _.any(this.curAttempts, a => a.goalNum == goalNum);
    if (!hasAttempt) {
      var goal = goals[goalIdx];
      var hash = this.curContextHashes[goalIdx];
      assert(!_.any(this.curAttempts, a => a.contextHash === hash));
      var attempt = new BruteAttempt(goal, goalNum, hash);
      this.curAttempts.push(attempt);
      attempt.run();
    }
  }
}
Brute.prototype.onUndoCallback = function(fromUser, undone, response) {
  this.update(response);
  goals.update(response);
}
Brute.prototype.onQueryResponse = function(requestType, request, response) {
  if (requestType == "query") {
    this.update(response);
    goals.update(response);
  }
}
Brute.prototype.onProofFound = function(attempt) {
  goals.onProofFound(attempt)
}
Brute.prototype.onProofInvalidated = function(attempt) {
  goals.onProofInvalidated(attempt)
}

Brute.prototype.onPtStartProcessing = function() {
  //console.log("Brute hook: onPtStartProcessing");
}
Brute.prototype.onPtEndProcessing = function() {
  //console.log("Brute hook: onPtEndProcessing");
}
Brute.prototype.onPtTacticsRefresh = function() {
  //console.log("Brute hook: onPtTacticsRefresh");
}

function getSolveTactics(goal) {
  var solveTacs = [
    "assumption",
    "reflexivity",
    "contradiction",
    "congruence",
    "discriminate",
    "tauto",
    "omega",
    "solve [auto]",
    //NOTE: these two are dangerous b/c they can unify evars
    "eassumption",
    "solve [eauto]"
  ];
  return solveTacs;
}

function getAdditiveTactics(goal) {
  //TODO: try destructive tactics too
  //TODO: support syntactic hueristics 
  //      (e.g. don't try reflexivity if goal doesn't have equality)

  var allHyps = _.map(getHyps(goal), h => h.hName);
  var lemmas = _.difference(namesPossiblyInScope, 
    //exclude bogus lemmas. The last thing in namesPossiblyInScope is the
    //  lemma we are trying to prove.
    ["modusponens", _.last(namesPossiblyInScope)]); 
  var vars = _.filter(allHyps, h => isLowerCase(h[0]));
  var hyps = _.filter(allHyps, h => !isLowerCase(h[0]));
  var hypsAndLemmas = _.union(lemmas, hyps);

  var additive = [
    "break_if; try discriminate",
    "break_match; try discriminate",
    "break_let; try discriminate",
    "break_if; try congruence",
    "break_match; try congruence",
    "break_let; try congruence",
    "progress repeat (break_match; try congruence)",
    "break_and",
    "break_exists",
  ];
  var additivePerLemma = [
    l => "exploit "+l+"; eauto; intro",
  ];
  var additivePerHyp = [  
    h => "inversion " + h,
    //Too expensive for now
    // h => "inversion " + h + "; try discriminate",
    // h => "inversion " + h + "; try congruence",
  ];  
  var additivePerNmHyp = [
    (h1, h2) => "copy "+h2+". apply " + h1 + " in " + h2,
    (h1, h2) => "copy "+h2+". eapply " + h1 + " in " + h2,
    (h1, h2) => "copy "+h2+". rewrite -> " + h1 + " in " + h2,
    (h1, h2) => "copy "+h2+". rewrite <- " + h1 + " in " + h2,
  ];

  var destructive = [
    "constructor",
    "econstructor",
    "eexists",
    "simpl in *",
    "left",
    "right",
    "split",
  ];
  var destructivePerHyp = [
    h => "rewrite -> " + h,
    h => "rewrite <- " + h,
    h => "inv " + h,
  ];
  var destructivePerVar = [
    v => "destruct " + v,
  ];
  var destructivePerNmHyp = [
    (h1, h2) => "apply " + h1 + " in " + h2,
    (h1, h2) => "eapply " + h1 + " in " + h2,
    (h1, h2) => "rewrite -> " + h1 + " in " + h2,
    (h1, h2) => "rewrite <- " + h1 + " in " + h2,
  ];

  var result = additive;  

  additivePerLemma.forEach(fn => 
    lemmas.forEach(l =>
      result.push(fn(l))))

  additivePerHyp.forEach(fn => 
    hyps.forEach(h =>
      result.push(fn(h))));

  //Too expensive for now
  // additivePerNmHyp.forEach(fn =>
  //   hypsAndLemmas.forEach(nm =>
  //     hyps.forEach(h =>
  //       result.push(fn(nm, h)))));

  return result;
}

//----- SCRATCH CODE ------
Brute.prototype.dummyFn = function() {
  var self = this;
  var pt = activeProofTree;

  var names = namesPossiblyInScope.reverse();
  var goalString = pt.curGoal().goalString;

  var curGoal = (isGoal(pt.curNode)) ? pt.curNode : pt.curNode.parent;
  var hypsFull = _(curGoal.hyps).clone().reverse();
  var hyps = _(hypsFull).map(function(h) { return h.hName; });
  var curNames = _(hyps).union(namesPossiblyInScope.reverse());

  var ts_all = masterTactics(pt);
  var ts_nodes = brute.pt.curNode.getTactics();
  var ts_strs = _.map(ts_nodes, "tactic");

  var isIdle = !_.any(brute.pt.tacticsWorklist);

  //TODO steer based on goal
  //goalIsForall
  //goalIsExists
  //goalIsConjunction
  //goalIsDisjunction
  //goalIsReflexive
  //brute.pt.curNode.goalString
  //TODO keep ghost proof tree in the background (?)

  var t = "tauto.";

  $("#loading").css("display", "none");
  $("#loading").css("display", "");
  $("#loading-text").text(nbsp + nbsp + "Trying " + t);

  return asyncQueryAndUndo(t)
      .then(delayPromise(0))
      .then(function(response) {
          if (isGood(response)) {
            //console.log("good response for: " + t);
          } else {
            //TODO
          }
      })
      .catch(outputError);
}