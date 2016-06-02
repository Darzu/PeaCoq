function Goals() {
    this.focusedGoals = [];
    this.unfocusedGoals = [];
}

window.goals = new Goals();

$(document).ready(function() {
});

Goals.prototype.update = function(response) {
    var self = this;
    var goals = window.brute.curGoals;
    var goalStrs = _.map(goals, getGoalStr);

    $("#goalStrs").html("");
    this.focusedGoals = [];

    if (goalStrs.length == 0) {
        $("#goalStrs").append("None.");
    }

    goalStrs.forEach(function(g) {
        self.focusedGoals.push(g);
        $("#goalStrs").append(g + "<br />");
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