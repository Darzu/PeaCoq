"use strict";

//algorithm:
//  for each g : goal
//    enqueue
//  on 

var solveTacs = [
  "assumption",
  "reflexivity",
  "contradiction",
  "congruence",
  "discriminate",
  "tauto",
  "omega",
  "solve [auto]"
];
var solveETacs = [
  "eassumption",
  "solve [eauto]"
];

function Brute() {
  console.log("Brute hook: [constr]");
}

window.brute = new Brute();

$(document).ready(function() {
  console.log("Brute hook: [doc. ready]");
});

Brute.prototype.onPtStartProcessing = function() {
  console.log("Brute hook: onPtStartProcessing");
}
Brute.prototype.onPtEndProcessing = function() {
  console.log("Brute hook: onPtEndProcessing");
}
Brute.prototype.onPtTacticsRefresh = function() {
  console.log("Brute hook: onPtTacticsRefresh");
}
Brute.prototype.onGoodQuery = function(request, response) {
  console.log("Brute hook: onGoodQuery: "+request);
  console.dir(response);

  var focused = response.rGoals.focused;
  var unfocused = response.rGoals.unfocused;

  for (var i = 0; i < focused.length; i++) {    
    var goalNum = i + 1;

    _.forEach(solveTacs, tac => { 
      var query = (goalNum > 1 ? goalNum + ": " : "") + tac + ".";

      //TODO enqueue
      asyncQueryAndUndo(query)
        .then(delayPromise(0))
        .then(function(response) {
            if (isGood(response)) {
              console.log("YAY!: " + query);
              //TODO validate
              //TODO add button
            } else {
              //TODO
            }
        })
        .catch(outputError);
    });
  }

  // if (unfocused.length > 0) {
  //   var hyps = _(response.rGoals.focused[0].gHyps).map(extractHypothesis).value()
  //   var hypsTxts = _(hyps).map(h => PT.showHypothesisText(h)).value();

  //   var goal = extractGoal(response.rGoals.focused[0].gGoal);
  //   var goalTxt = showTermText(goal);

  //   console.log(goalTxt)
  // }
}
Brute.prototype.onUndoCallback = function(response) {
  console.log("Brute hook: onUndoCallback: ");
  console.dir(response);
}

Brute.prototype.myFn = function() {
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
            console.log("good response for: " + t);
          } else {
            //TODO
          }
      })
      .catch(outputError);
}