"use strict";

//TODO:
// - add priorities to async requests
//   - and/or: wait until proof process is idle before trying proofs

//Algorithm:
//  after proof cursor changes:
//    check validity of in-progress proofs
//    create new attempts for goals not in progress

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

function getHypStrs(goal) {
  return _.map(goal.gHyps, h => PT.showHypothesisText(extractHypothesis(h)))
}
function getGoalStr(goal) {
  return showTermText(extractGoal(goal.gGoal))
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
  this.update();
}
BruteAttempt.prototype.hasSolution = function() {
  return !!this.solution;
}
BruteAttempt.prototype.update = function() {
  var self = this;
  var queryGoalNum = this.goalNum;
  var isQueryValid = () => {
    return self.isValid && self.goalNum === queryGoalNum && !self.hasSolution()
  }

  _.forEach(solveTacs, tac => {
    var queryPrefix = queryGoalNum > 1 ? queryGoalNum + ": " : "";
    var query = queryPrefix + tac + ".";

    //TODO track whether or not the depth finished
    asyncQueryAndUndo(query, () => !isQueryValid)
      .then(delayPromise(0))
      .then(function(response) {
          if (isGood(response)) {
            if (isQueryValid()) {      
              self.solution = query;
              brute.onProofFound(self);
            }
          }
      })
      .catch(outputError);
  })  
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
      var attempt = new BruteAttempt(goal, goalNum, hash);
      this.curAttempts.push(attempt);
      attempt.update();
    }
  }
}
Brute.prototype.onUndoCallback = function(response) {
  this.update(response);
}
Brute.prototype.onQueryResponse = function(response) {
  this.update(response);
}
Brute.prototype.onProofFound = function(attempt) {
  var sln = attempt.solution;
  console.log("YAY! " + sln);
}
Brute.prototype.onProofInvalidated = function(attempt) {
  var sln = attempt.solution;
  console.log("invalidated. " + sln);
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

//----- SCRATCH CODE ------
Brute.prototype.dummyFn = function() {
  var self = this;
  var pt = activeProofTree;

  var names = namesPossiblyInScope.reverse();
  var goalString = pt.curGoal().goalString;

  var curGoal = (isGoal(pt.curNode)) ? pt.curNode : pt.curNode.parent;
  var curHypsFull = _(curGoal.hyps).clone().reverse();
  var curHyps = _(curHypsFull).map(function(h) { return h.hName; });
  var curNames = _(curHyps).union(namesPossiblyInScope.reverse());

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