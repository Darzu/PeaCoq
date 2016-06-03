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
        if (attempt.isValid) {
            var g = {"goalName": getGoalStr(attempt.goal)};
            g["goalSln"] = attempt.solution;
            g["isSlnMinimal"] = attempt.isSlnMinimal;
            self.focusedGoals.push(g); 
        }
    });

    this.drawPane();
};

Goals.prototype.drawPane = function() {
    var id = "#goalStrs";
    var solvedGoals = _.size(_.filter(this.focusedGoals,goalHasValidSln));
    var solvedMinimalGoals = _.size(_.filter(this.focusedGoals,function(g) { return g.isSlnMinimal}));
    if (solvedGoals == 0) {
        $("#solvedGoalsCount").html("");
    } else {
        $("#solvedGoalsCount").html(solvedGoals);
    }
    if (solvedGoals == solvedMinimalGoals) {
        $("#solvedGoalsCount").addClass("label-primary").removeClass("label-danger");
    } else {
        $("#solvedGoalsCount").addClass("label label-danger").removeClass("label-primary");
    }

    $("#goalStrs").html("");
    if (this.focusedGoals.length == 0) {
        $(id).append("None.");
    }
    this.focusedGoals.forEach(function(g,i) {
        if (goalHasValidSln(g)) {
            $(id).append("<code>" + g.goalName + ":</code>" + minimalBadge(g) + "<pre class=\"importBlock\" data-dismiss=\"modal\">" + g.goalSln + "</pre>" + "<br />");
        } else {
            $(id).append(g.goalName + "<br />");
        }
    });
    var self = this;

    $(".importBlock").click(function() {
        console.log($(this).html());
        self.injectCode($(this).html());
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
Goals.prototype.onMinimalProofFound = function(attempt) {
  var sln = attempt.solution;
  var goalNum = attempt.goalNum;
  this.focusedGoals[goalNum - 1].goalSln = sln;
  this.update("fake");
}

Goals.prototype.injectCode = function(code) {
    CodeMirror.showHint(doc.cm, function(cm) {
        var completions = [code + " "];
        return {
            list: completions,
            from: doc.cm.getCursor(),
            to: doc.cm.getCursor(),
            _handlers: {
                "pick": [function() {processToPos(doc.cm.getCursor());}]
            }
        };}
     , {});
}

Goals.prototype.suggestCompletions = function(completionList) {
    cList = [];
    for (i in completionList) {
        var code = this.focusedGoals[i].goalSln + " ";
        cList.push(code);
    }

    CodeMirror.showHint(doc.cm, function(cm) {
        var completions = cList;
        return {
            list: completions,
            from: doc.cm.getCursor(),
            to: doc.cm.getCursor(),
            _handlers: {
                "pick": [function() {processToPos(doc.cm.getCursor());}]
            }
        };}
     , {completeSingle: false
        });
}

Goals.prototype.trySuggestions = function() {
    var solvedGoals = _.size(_.filter(this.focusedGoals,goalHasValidSln));
    if (solvedGoals > 0) {
        cList = [];
        _.filter(this.focusedGoals,goalHasValidSln).forEach(function(g,i) {
            cList.push(i);
        });
        this.suggestCompletions(cList);
    }
}

function goalHasValidSln(g) {
    return !_.isNull(g.goalSln) && g.goalSln != "";
}

function minimalBadge(attempt) {
    if (attempt.isSlnMinimal) {
        return "&nbsp;&nbsp;<span class=\"label label-primary\">minimal</span>";
    } else {
        return "";
    }
}
