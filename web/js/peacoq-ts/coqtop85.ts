/// <reference path="coq85.ts"/>

/*
  This queue guarantees that requests are pushed one after the other, and that
  failure of a request cascades and cancels the following ones.
*/
class RequestQueue {
  queue: Promise<any>;
  constructor() {
    this.queue = Promise.resolve();
  }
  push(f: () => Promise<any>) {
    var self = this;
    var res = this.queue.then(function() { return f(); });
    this.queue = res.catch(function() { self.queue = Promise.resolve(); });
    return res;
  }
}

var requests = new RequestQueue();

function unbsp(s: string): string {
  return s.replace(/ /g, ' ');
}

function trimSpacesAround(s: string): string {
  return s.replace(/^\s+|\s+$/g, '');
}

// TODO: This should be made robust to multiple calls (sequencing should be
// enforced)

function coqtop(
  command: string,
  input: Object,
  silent?: boolean
  ): Promise<any> {
  return requests.push(() => new Promise(function(onFulfilled, onRejected: (v: ValueFail) => any) {
    $.ajax({
      type: 'POST',
      url: command,
      data: {
        data: JSON.stringify(input)
      },
      async: true,
      error: function() {
        console.log("Server did not respond!");
      },
      success: function(response) {
        var result = response[0];
        var stateId = response[1][0];
        var editId = response[1][1];
        var messages = response[2][0];
        var feedback = response[2][1];
        //if (!silent) { console.log("Response: ", response, feedback, messages); }
        // This is slow, disabled until it is useful
        // TODO: make this processing asynchronous to not hang UI
        /*
        _(feedback).each(function(x) {
          var f = new Feedback(x);
          onFeedback(f);
        });
        */
        _(messages).each(function(x) {
          var m = new Message(x);
          onMessage(m);
        });

        //console.log("Result: ", result);
        switch (result.tag) {
          case "ValueGood":
            onFulfilled(result.contents);
            break;
          case "ValueFail":
            onRejected(new ValueFail(result.contents));
            break;
          default:
            throw "result.tag was neither ValueGood nor ValueFail";
        }
      }
    });
  }));
}

function peaCoqAddPrime(s: string): Promise<any> {
  console.log("Add'", s);
  var res =
    coqtop("add'", s)
      .then(
      (r) => {
        r = {
          "stateId": r[0],
          "eitherNullStateId": r[1][0],
          "output": r[1][0],
        };
        return r;
        //console.log("[@" + stateId + "] Added", eitherNullStateId, output);
      })
    ;
  return res;
}

function peaCoqEditAt(sid: number): Promise<Object> {
  console.log("EditAt", sid);
  return coqtop("editat", sid);
}

type PeaCoqHyp = {
  name: string;
  maybeTerm: Maybe<ConstrExpr>;
  type: ConstrExpr;
};
type PeaCoqGoal = {
  hyps: PeaCoqHyp[];
  concl: ConstrExpr;
};
type PeaCoqContext = Array<PeaCoqGoal>;

function peaCoqGetContext(): Promise<PeaCoqContext> {
  return (
    peaCoqQueryPrime("PeaCoqGetContext.")
      .then(
      (context) => {
        // TODO: don't use eval
        //console.log(context);
        var term = eval(context);
        return term;
      })
      .catch(
        (vf: ValueFail) => {
          // most likely not in proof mode
          return [];
        }
      )
    );
}

class Goal {
  goalId: number;
  goalHyp: Array<string>;
  goalCcl: string;
  constructor(g) {
    this.goalId = g[0];
    this.goalHyp = _(g[1]).map(unbsp).value();
    this.goalCcl = unbsp(g[2]);
  }
  toString() {
    var res = "";//"Goal " + this.goalId + "\n\n";
    _(this.goalHyp).each(function(h) {
      res += h + "\n";
    });
    _(_.range(80)).each(function() { res += '-'; });
    res += "\n" + this.goalCcl;
    return res;
  }
}

type BeforeAfter = {
  before: Array<Goal>;
  after: Array<Goal>;
};

class Goals {
  "fgGoals": Array<Goal>;
  "bgGoals": Array<BeforeAfter>;
  "shelvedGoals": Array<Goal>;
  "givenUpGoals": Array<Goal>;
  constructor(maybeGoals) {
    if (!maybeGoals) {
      this.fgGoals = [];
      this.bgGoals = [];
      this.shelvedGoals = [];
      this.givenUpGoals = [];
    } else {
      this.fgGoals = _(maybeGoals[0]).map(function(g) {
        return new Goal(g);
      }).value();
      this.bgGoals = _(maybeGoals[1]).map(function(ba) {
        return {
          "before": _(ba[0]).map(function(b) { return new Goal(b); }).value(),
          "after": _(ba[1]).map(function(b) { return new Goal(b); }).value(),
        };
      }).value();
      this.shelvedGoals = _(maybeGoals[2]).map(function(g) {
        return new Goal(g);
      }).value();
      this.givenUpGoals = _(maybeGoals[3]).map(function(g) {
        return new Goal(g);
      }).value();
    }
  }
}

function peaCoqGoal(): Promise<Goals> {
  console.log("Goal");
  return (
    coqtop("goal", [])
      .then(
      (maybeGoals) => {
        //console.log("maybeGoals", maybeGoals);
        var goals = new Goals(maybeGoals);
        // weird, maybeGoals is an array of length 4 with 3 empty
        //console.log("Goal", goals);
        return goals;
      })
      .catch(
      (vf: ValueFail) => {
        return [];
      }
      )
    );
}

// function peaCoqInit() {
//     console.log("Init");
//     coqtop("init", null, function(sid) {
//         //console.log("Initialized, current state Id: ", sid);
//     });
// }

function peaCoqQueryPrime(s: string): Promise<string> {
  console.log("Query'", s);
  return coqtop("query'", s);
}

function peaCoqPrintAST(sid: number): Promise<CoqXMLTree> {
  console.log("PrintAST", sid);
  return coqtop("printast", sid).then(function(r) {
    var tree = new CoqXMLTree(r);
    console.log("PrintAST\n", r.toString());
    return tree;
  });
}

class Status {
  statusPath: Array<string>;
  statusProofName: string;
  statusAllProofs: string;
  statusProofNum: number;
  constructor(status) {
    this.statusPath = status[0];
    this.statusProofName = status[1];
    this.statusAllProofs = status[2];
    this.statusProofNum = status[3];
  }
}

function peaCoqStatus(b: boolean): Promise<Status> {
  console.log("Status");
  return (
    coqtop("status", b)
      .then(
      (s) => {
        return new Status(s);
      })
      .catch(
      (vf: ValueFail) => {
        throw "OOPS: peaCoqStatus";
      }
      )
    );
}

class ValueFail {
  stateId: number;
  location: string;
  message: string;
  constructor(v) {
    this.stateId = v[0];
    this.location = v[1];
    this.message = trimSpacesAround(unbsp(v[2]));
  }
}

function mkMessageLevel(m): MessageLevel {
  switch (m.tag) {
    case "Debug":
      return new Debug(m.contents);
    case "Error":
      return new Error();
    case "Info":
      return new Info();
    case "Notice":
      return new Notice();
    case "Warning":
      return new Warning();
    default:
      throw ("Unknown message level: " + m.tag);
  };
}

class MessageLevel { }

class Debug extends MessageLevel {
  debug: string;
  constructor(s) {
    super();
    this.debug = s;
  }
  toString() {
    return "Debug(" + this.debug + ")";
  }
}

class MyError extends MessageLevel {
  constructor() { super(); }
  toString() { return "Error"; }
}

class Info extends MessageLevel {
  constructor() { super(); }
  toString() { return "Info"; }
}

class Notice extends MessageLevel {
  constructor() { super(); }
  toString() { return "Notice"; }
}

class Warning extends MessageLevel {
  constructor() { super(); }
  toString() { return "Warning"; }
}

class Message {
  level: MessageLevel;
  content: string;
  constructor(m) {
    this.level = mkMessageLevel(m[0]);
    this.content = unbsp(m[1]);
  }
  toString() {
    return (
      "[" + this.level.toString() + "]\n" + this.content
      );
  }
}

class Feedback {
  editOrState: string;
  editOrStateId: number;
  feedbackContent: FeedbackContent;
  routeId: number;
  constructor(f) {
    switch (f[0].tag) {
      case "State":
        this.editOrState = "state";
        break;
      case "Edit":
        this.editOrState = "edit";
        break;
      default:
        throw "Feedback tag was neither State nor Edit";
    };
    this.editOrStateId = f[0].contents;
    this.feedbackContent = mkFeedbackContent(f[1]);
    this.routeId = f[2];
  }
  toString() {
    return (
      "Feedback(" + this.editOrState + ", " + this.editOrStateId + ", " +
      this.feedbackContent + ", " + this.routeId + ")"
      );
  }
}

function mkFeedbackContent(f) {
  this.tag = f.tag;
  switch (this.tag) {
    case "AddedAxiom":
    case "Custom":
    case "ErrorMsg":
    case "FileDependency":
    case "FileLoaded":
    case "GlobDef":
    case "GlobRef":
    case "Goals":
    case "Message":
      //console.log("TODO: FeedbackContent for " + this.tag, f);
      break;
    case "Processed":
      return new Processed();
    case "ProcessingIn":
      return new ProcessingIn(f.contents);
    case "WorkerStatus":
      console.log("TODO: FeedbackContent for " + this.tag, f);
      break;
    // other tags don't need fields
    default:
      throw ("Unknown FeedbackContent tag: " + this.tag);
  }
}

class FeedbackContent { }

class Processed extends FeedbackContent {
  toString() { return "Processed"; }
}

class ProcessingIn extends FeedbackContent {
  s: string;
  constructor(s) {
    super();
    this.s = s;
  }
  toString() {
    return "ProcessingIn(" + this.s + ")";
  }
}

class CoqXMLTree {
  rootLabel: LocatedCoqXMLTag;
  subForest: Array<CoqXMLTree>;
  constructor(t) {
    this.rootLabel = new LocatedCoqXMLTag(t[0]);
    this.subForest = _(t[1]).map(function(t) {
      return new CoqXMLTree(t);
    }).value();
  }
  toString(depth: number) {
    var res = "";
    if (typeof depth === "undefined") {
      depth = 0;
    }
    _(_.range(depth)).each(function() {
      res += "  ";
    });
    res += "`- " + this.rootLabel.toString() + "\n";
    _(this.subForest).each(function(t: CoqXMLTree) {
      res += t.toString(depth + 1);
    });
    return res;
  }
}

class LocatedCoqXMLTag {
  maybeLocation: any;
  coqXMLTag: CoqXMLTag;
  constructor(t) {
    this.maybeLocation = t[0];
    this.coqXMLTag = mkCoqXMLTag(t[1]);
  }
  toString() {
    return this.coqXMLTag.toString();
  }
}

class CoqXMLTag { }

function mkCoqXMLTag(t): CoqXMLTag {
  var c = t.contents;
  switch (t.tag) {
    case "Apply":
      return new Apply();
      break;
    case "Constant":
      return new Constant(c);
      break;
    case "Definition":
      return new Definition(c[0], c[1]);
      break;
    case "Gallina":
      return new Gallina();
      break;
    case "Ltac":
      return new Ltac(c);
      break;
    case "Operator":
      return new Operator(c[0], c[1]);
      break;
    case "Proof":
      return new Proof();
      break;
    case "QED":
      return new QED();
      break;
    case "Recurse":
      return new Recurse();
      break;
    case "SectionSubsetDescr":
      return new SectionSubsetDescr(c);
      break;
    case "Theorem":
      return new Theorem(c[0], c[1]);
      break;
    case "Token":
      return new Token(c);
      break;
    case "Typed":
      return new Typed();
      break;
    default:
      throw ("Unknown CoqXMLTag: " + t.tag);
      break;
  };
}

class Apply extends CoqXMLTag {
  toString() { return "Apply"; }
}

class Constant extends CoqXMLTag {
  constant: string;
  constructor(s) {
    super();
    this.constant = s;
  }
  toString() { return "Constant(" + this.constant + ")"; }
}

class Definition extends CoqXMLTag {
  a: string;
  b: string;
  constructor(a, b) {
    super();
    this.a = a;
    this.b = b;
  }
  toString() {
    return "Definition(" + this.a + ", " + this.b + ")";
  }
}

class Gallina extends CoqXMLTag {
  toString = function() { return "Gallina"; }
}

class Ltac extends CoqXMLTag {
  s: string;
  constructor(s) {
    super();
    this.s = s;
  }
  toString() { return "Ltac(" + this.s + ")"; }
}

class Operator extends CoqXMLTag {
  s: string;
  ms: string;
  constructor(s, ms) {
    super();
    this.s = s;
    this.ms = ms;
  }
  toString() { return "Operator(" + this.s + ", " + this.ms + ")"; }
}

class Proof extends CoqXMLTag {
  toString() { return "Proof"; }
}

class QED extends CoqXMLTag {
  toString() { return "QED"; }
}

class Recurse extends CoqXMLTag {
  toString() { return "Recurse"; }
}

class SectionSubsetDescr extends CoqXMLTag {
  s: string;
  constructor(s) {
    super();
    this.s = s;
  }
  toString() { return "SectionSubsetDescr(" + this.s + ")"; }
}

class Theorem extends CoqXMLTag {
  a: string;
  b: string;
  constructor(a, b) {
    super();
    this.a = a;
    this.b = b;
  }
  toString() { return "Theorem(" + this.a + ", " + this.b + ")"; }
}

class Token extends CoqXMLTag {
  s: string;
  constructor(s) {
    super();
    this.s = s;
  }
  toString() { return "Token(" + this.s + ")"; }
}

class Typed extends CoqXMLTag {
  toString() { return "Typed"; }
}
