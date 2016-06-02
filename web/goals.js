function Goals() {
    this.focusedGoals = [];
    this.unfocusedGoals = [];
}

window.goals = new Goals();

$(document).ready(function() {
});

Goals.prototype.update = function(response) {
    console.log(response)
    var self = this;
    var goals = window.brute.curGoals;
    
    this.focusedGoals = [];

    window.brute.curAttempts.forEach(function(attempt) {
        var g = {"goalName": getGoalStr(attempt.goal)};
        if (attempt.isValid) {
            g["goalSln"] = attempt.solution;
        }
        self.focusedGoals.push(g);
    });

    this.drawPane();
};

Goals.prototype.drawPane = function() {
    console.log("drawing goal pane");
    var id = "#goalStrs";
    $("#goalStrs").html("");
    if (this.focusedGoals.length == 0) {
        $(id).append("None.");
    }
    this.focusedGoals.forEach(function(g) {
        if (g.goalSln != "") {
            $(id).append("<b>" + g.goalName + ":</b> " + g.goalSln + "<br />");
        } else {
            $(id).append(g.goalName + "<br />");
        }
    })
}

Goals.prototype.onProofFound = function(attempt) {
  var sln = attempt.solution;
  var goalNum = attempt.goalNum;
  this.focusedGoals[goalNum - 1].goalSln = sln;
  console.log("YAY! " + sln + " " + goalNum);
  this.drawPane();
}
Goals.prototype.onProofInvalidated = function(attempt) {
  var sln = attempt.solution;
  var goalNum = attempt.goalNum;
  console.log("invalidated. " + sln);
}

Goals.prototype.injectCode = function(code) {
    CodeMirror.showHint(doc.cm, function(cm) {
        var completions = [code];
        return {
            list: completions,
            from: doc.cm.getCursor(),
            to: doc.cm.getCursor()
        };}
     , {});
}