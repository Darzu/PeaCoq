"use strict";

var MAX_DEPTH = 3;

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

function BruteAttempt(goal, goalNum, contextHash, maxDepth) {
  //TODO: can we get away with tracking less state?
  this.goal = goal;
  this.goalNum = goalNum;
  if (!contextHash)
    contextHash = getContextHash(goal)
  this.contextHash = contextHash;
  this.isValid = true;
  this.solution = null;
  this.depth = 0;
  this.maxDepth = maxDepth;
  this.slnChain = [];
  this.isSlnMinimal = false;
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
function mkQuery(tactics, goalNum, delimiter) {
  if (!delimiter) {
    delimiter = goalNum === 1 ? ". " : "; "
  }
  var queryPrefix = goalNum > 1 ? goalNum + ": " : "";
  var query = queryPrefix + tactics.join(delimiter) + ".";
  return query;
}
BruteAttempt.prototype.run = function() {
  var self = this;
  
  if (!self.isValid || (self.hasSolution() && self.isSlnMinimal))
    return;
 
  var mkQueries = (tactics, mkTacQuery) => {
    if (!mkTacQuery) {
      mkTacQuery = t => t;
    }
    var queries = [];
    tactics.forEach(tac => {
      var chain = self.slnChain.concat([mkTacQuery(tac)]);
      var query = mkQuery(chain, self.goalNum, "; ");
      queries.push(query);
    });
    return queries;
  }
  var mkDict = (keys, vals) => {
    var m = {}
    for (var i = 0; i < vals.length; i++) {
      m[keys[i]] = vals[i];
    }
    return m;
  }

  var runAddTacs = () => {
    var tactics = getAdditiveTactics(self.goal);
    var mkTacQuery = (t) => {
      //This ensures the query makes progress, doesn't just add duplicates,
      //  and doesn't introduce new goals
      return "repeat clear_dup; progress ("+t+"; repeat clear_dup); []"
    }
    var queries = mkQueries(tactics, mkTacQuery);
    var qToTacs = mkDict(queries, tactics);
    var onAddTacSucc = (query, response) => {
      var tactic = qToTacs[query];
      self.slnChain.push(tactic);
      self.run();
    }
    var onAllAddTried = () => {
      console.log("Failed to make any progress on "+self.contextHash+" at depth: " + self.depth);
    }
    self.tryQueries(queries, onAddTacSucc, onAllAddTried, true);
  }
  var runSolveTacs = () => {
    var tactics = getSolveTactics(self.goal);
    var queries = mkQueries(tactics);
    var qToTacs = mkDict(queries, tactics);
    var onSolveTacSucc = (query, response) => { 
      var tac = qToTacs[query];
      self.slnChain.push(tac);
      var chain = self.slnChain;
      var sln = mkQuery(chain, self.goalNum);
      self.solution = sln;
      brute.onProofFound(self);
      self.run()
    }
    var onAllSolveTried = () => {
      if (self.depth < self.maxDepth) {
        self.depth++;
        self.run();
      }
    }
    self.tryQueries(queries, onSolveTacSucc, onAllSolveTried, true);
  }
  var runMkSlnMin = () => {
    var rmvOnePerms = (a) => {
      var ps = _.map(a, (e, i) => {
        var r = _.clone(a)
        r.splice(i, 1);
        return r
      })
      return ps;
    }
    var perms = rmvOnePerms(self.slnChain);   
    perms.pop(); //the last tactic is always necessary 
    var queries = _.map(perms, a => mkQuery(a, self.goalNum, "; "));
    var qToIdx = mkDict(queries, _.map(queries, (e,i) => i));
    var onMkSmaller = (query, response) => { 
      var idx = qToIdx[query];
      self.slnChain = perms[idx];
      self.solution = mkQuery(self.slnChain, self.goalNum);
      self.run();
    }
    var onCantMkSmaller = () => {
      self.isSlnMinimal = true;
      brute.onMinimalProofFound(self);
    }
    self.tryQueries(queries, onMkSmaller, onCantMkSmaller, true);
  }

  if (self.hasSolution() && !self.isSlnMinimal) {
    runMkSlnMin();
  } else if (self.slnChain.length < self.depth) {
    runAddTacs();
  } else {
    runSolveTacs();    
  }
}
BruteAttempt.prototype.tryQueries = function(queries, onQuerySuccess, onAllTried, stopAfterSucc) {
  var self = this;
  var queryGoalNum = this.goalNum;
  var queryDepth = this.depth;
  var anySuccess = false;

  var isQueryValid = () => {
    return self.isValid 
      && self.goalNum === queryGoalNum 
      && self.depth === queryDepth
      && !(stopAfterSucc && anySuccess)
  }

  var promises = []

  _.forEach(queries, query => { 
    var promise = asyncQueryAndUndo(query, () => !isQueryValid(), true)
      .then(delayPromise(0))
      .then(function(response) {
        if (isGood(response)) {
          if (isQueryValid()) {
            anySuccess = true;
            onQuerySuccess(query, response);
          }
        }
      })
      .catch(outputError);

    promises.push(promise)
  })  

  Promise.all(promises)
    .then(function() {
      onAllTried();
    });
}

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
      var attempt = new BruteAttempt(goal, goalNum, hash, MAX_DEPTH);
      this.curAttempts.push(attempt);
      attempt.run();
    }
  }
}
Brute.prototype.onUndoCallback = function(fromUser, undone, response) {
  this.update(response);
  //goals.update(response);
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
Brute.prototype.onMinimalProofFound = function(attempt) {
  console.log("WOOT! Min sln! " + attempt.solution); 
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