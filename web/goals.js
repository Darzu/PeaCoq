function Goals() {
    this.focusedGoals = [];
    this.unfocusedGoals = [];
}

window.goals = new Goals();

$(document).ready(function() {
});

Goals.prototype.update = function(response) {
    var self = this;
    var goals = brute.curGoals;
    var goalStrs = _.map(goals, getGoalStr);
//    goalStrs.forEach(g) {
//        $("#focusedGoals").append(g);
//    }

    console.log("unfocusedGoals " + response.rGoals.unfocused.length);

    response.rGoals.focused.forEach(function(g) {
        self.focusedGoals.push(showTermText(extractGoal(g.gGoal)));
        $("#focusedGoals").append(getGoalStr(g));
    });

    if (response.rGoals.unfocused.length == 0) {
        $("#unfocusedGoals").html("None");
    } else {
        $("#unfocusedGoals").html("");
    }

    response.rGoals.unfocused.forEach(function(g) {
        console.log("they exist!");
        self.unfocusedGoals.push(showTermText(extractGoal(g.gGoal)));
        $("#unfocusedGoals").append(showTermText(extractGoal(g.gGoal)) + "\n")
    }); 
};

Goals.prototype.onProofFound = function(attempt) {
  var sln = attempt.solution;
  var goalNum = attempt.goalNum;
  console.log("YAY! " + sln);
}
Goals.prototype.onProofInvalidated = function(attempt) {
  var sln = attempt.solution;
  var goalNum = attempt.goalNum;
  console.log("invalidated. " + sln);
}