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
            self.focusedGoals.push(g); 
        }
    });

    this.drawPane();
};

Goals.prototype.drawPane = function() {
    var id = "#goalStrs";
    var solvedGoals = _.size(_.filter(this.focusedGoals,function(g){ return (!_.isNull(g.goalSln) && g.goalSln != ""); }));
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
        if (!_.isNull(g.goalSln) && g.goalSln != "") {
            $(id).append("<code>" + g.goalName + ":</code>" +  "<pre class=\"importBlock\" data-dismiss=\"modal\">" + g.goalSln + "</pre>" + "<br />");
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

Goals.prototype.injectCode = function(code) {
    CodeMirror.showHint(doc.cm, function(cm) {
        var completions = [" " + code + " "];
        return {
            list: completions,
            from: doc.cm.getCursor(),
            to: doc.cm.getCursor()
        };}
     , {});
}

Goals.prototype.suggestCompletions = function(completionList) {
    cList = [];
    for (i in completionList) {
        var code = " " + this.focusedGoals[i].goalSln;
        cList.push(code);
    }
    
    CodeMirror.showHint(doc.cm, function(cm) {
        var completions = cList;
        return {
            list: completions,
            from: doc.cm.getCursor(),
            to: doc.cm.getCursor()
        };}
     , {completeSingle: false
        });
}

Goals.prototype.trySuggestions = function() {
    var solvedGoals = _.size(_.filter(this.focusedGoals,function(g){ return (!_.isNull(g.goalSln) && g.goalSln != ""); }));
    if (solvedGoals > 0) {
        cList = [];
        this.focusedGoals.forEach(function(g,i) {
            cList.push(i);
        });
        this.suggestCompletions(cList);
    }
}

function getGoalBtn(index) {
    return "<button class=\"btn btn-default importButton close\" type=\"button\"  data-dismiss=\"modal\" value=\"" + index + "\">Import Solution</button>";
}
