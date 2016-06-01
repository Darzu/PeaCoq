function Goals() {
    this.focusedGoals = [];
    this.unfocusedGoals = [];
}

Goals.prototype.update = function(response) {
    var self = this;
   // $("focusedGoals").html("");
    response.rGoals.focused.forEach(function(g) {
        self.focusedGoals.push(showTermText(extractGoal(g.gGoal)));
        $("#focusedGoals").html(showTermText(extractGoal(g.gGoal)))
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
  //  $("#focusedGoals").html(this.focusedGoals[0]);
  //  $("#unfocusedGoals").html()
};