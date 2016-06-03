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
    var id = "#goalStrs";
    var solvedGoals = _.size(_.filter(this.focusedGoals,function(g){ return g.goalSln != ""; }));
    if (solvedGoals == 0) {
        $("#solvedGoalsCount").html("");
    } else {
        $("#solvedGoalsCount").html(solvedGoals);
    }

    $("#goalStrs").html("");
    if (this.focusedGoals.length == 0) {
        $(id).append("None.");
    }
    this.focusedGoals.forEach(function(g,i) {
        if (g.goalSln != "") {
            $(id).append("<b>" + g.goalName + ":</b> " + g.goalSln + getGoalBtn(i) + "<br />");
        } else {
            $(id).append(g.goalName + "<br />");
        }
    });
    var self = this;
    $(".importButton").click(function() {
        self.injectCode($(this).val());
    });
}

Goals.prototype.onProofFound = function(attempt) {
  var sln = attempt.solution;
  var goalNum = attempt.goalNum;
  this.focusedGoals[goalNum - 1].goalSln = sln;
  console.log("YAY! " + sln + " " + goalNum);
  this.update("fake");
}
Goals.prototype.onProofInvalidated = function(attempt) {
  var sln = attempt.solution;
  var goalNum = attempt.goalNum;
  console.log("invalidated. " + sln);
  this.update("fake");
}

Goals.prototype.injectCode = function(i) {
    var code = " " + this.focusedGoals[i].goalSln;
    CodeMirror.showHint(doc.cm, function(cm) {
        var completions = [code];
        return {
            list: completions,
            from: doc.cm.getCursor(),
            to: doc.cm.getCursor()
        };}
     , {});
}


function getGoalBtn(index) {
    return "<button class=\"btn btn-default importButton close\" type=\"button\"  data-dismiss=\"modal\" value=\"" + index + "\">Import Solution</button>";
}