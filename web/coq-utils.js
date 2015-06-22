var vernacularPrefixes = [
    "*",
    "+",
    "-",
    "{",
    "}",
    "Abort",
    "About",
    "Add Field",
    "Add Legacy Abstract Ring",
    "Add Legacy Abstract Semi Ring",
    "Add Legacy Field",
    "Add Legacy Ring",
    "Add Legacy Semi Ring",
    "Add Legacy Semi Ring",
    "Add LoadPath",
    "Add ML Path",
    "Add Morphism",
    "Add Parametric Morphism",
    "Add Parametric Relation",
    "Add Printing If ident",
    "Add Printing Let ident",
    "Add Rec LoadPath",
    "Add Rec ML Path",
    "Add Relation",
    "Add Ring",
    "Add Setoid",
    "Admit Obligations",
    "Admitted",
    "Arguments",
    "Axiom",
    "Back",
    "BackTo",
    "Backtrack",
    "Bind Scope",
    "Canonical Structure",
    "Cd",
    "Check",
    "Class",
    "Close Scope",
    "Coercion",
    "CoFixpoint",
    "CoInductive",
    "CoInductive (and coercions)",
    "Combined Scheme",
    "Compute",
    "Conjecture",
    "Context",
    "Corollary",
    "CreateHintDb",
    "Declare Implicit Tactic",
    "Declare Instance",
    "Declare Left Step",
    "Declare ML Module",
    "Declare Right Step",
    "Defined",
    "Definition",
    "Delimit Scope",
    "Derive Dependent Inversion",
    "Derive Dependent Inversion_clear",
    "Derive Inversion",
    "Derive Inversion_clear",
    "Drop",
    "End",
    "Eval",
    "Example",
    "Existential",
    "Existing Class",
    "Existing Instance",
    "Existing Instances",
    "Export",
    "Extract Constant",
    "Extract Inductive",
    "Extraction",
    "Extraction Blacklist",
    "Extraction Implicit",
    "Extraction Inline",
    "Extraction Language",
    "Extraction Library",
    "Extraction NoInline",
    "Fact",
    "Fixpoint",
    "Focus",
    "Function",
    "Functional Scheme",
    "Generalizable Variables",
    "Global",
    "Global Arguments",
    "Global Set",
    "Global Unset",
    "Goal",
    "Grab Existential Variables",
    "Guarded",
    "Hint",
    "Hint Constructors",
    "Hint Extern",
    "Hint Immediate",
    "Hint Opaque",
    "Hint Resolve",
    "Hint Rewrite",
    "Hint Transparent",
    "Hint Unfold",
    "Hypotheses",
    "Hypothesis",
    "Identity Coercion",
    "Implicit Arguments",
    "Implicit Types",
    "Import",
    "Include",
    "Inductive",
    "Infix",
    "Inline",
    "Inspect",
    "Instance",
    "Lemma",
    "Let",
    "Load",
    "Load Verbose",
    "Local",
    "Local Arguments",
    "Local Coercion",
    "Local Set",
    "Local Strategy",
    "Local Unset",
    "Locate",
    "Locate File",
    "Locate Library",
    "Locate Module",
    "Ltac",
    "Module",
    "Module Type",
    "Next Obligation",
    "Notation",
    "Obligation",
    "Obligation Tactic",
    "Obligations",
    "Opaque",
    "Open Scope",
    "Parameter",
    "Parameters",
    "Preterm",
    "Print",
    "Print All",
    "Print Assumptions",
    "Print Canonical Projections",
    "Print Classes",
    "Print Coercion Paths",
    "Print Coercions",
    "Print Extraction Inline",
    "Print Grammar constr",
    "Print Grammar pattern",
    "Print Graph",
    "Print Hint",
    "Print HintDb",
    "Print Implicit",
    "Print Libraries",
    "Print LoadPath",
    "Print Ltac",
    "Print ML Modules",
    "Print ML Path",
    "Print Module",
    "Print Module Type",
    "Print Opaque Dependencies",
    "Print Options",
    "Print Scope",
    "Print Scopes",
    "Print Section",
    "Print Sorted Universes",
    "Print Table Printing If",
    "Print Table Printing Let",
    "Print Tables",
    "Print Term",
    "Print Universes",
    "Print Visibility",
    "Print XML",
    "Program Definition",
    "Program Fixpoint",
    "Program Instance",
    "Program Lemma",
    "Proof",
    "Proof using",
    "Proof with",
    "Proposition",
    "Pwd",
    "Qed",
    "Quit",
    "Record",
    "Recursive Extraction",
    "Recursive Extraction Library",
    "Remark",
    "Remove LoadPath",
    "Remove Printing If ident",
    "Remove Printing Let ident",
    "Require",
    "Require Export",
    "Reserved Notation",
    "Reset",
    "Reset Extraction Inline",
    "Reset Initial",
    "Restart",
    "Restore State",
    "Save",
    "Scheme",
    "Scheme Equality",
    "Search",
    "SearchAbout",
    "SearchPattern",
    "SearchRewrite",
    "Section",
    "Separate Extraction",
    "Set",
    "Set Automatic Coercions Import",
    "Set Automatic Introduction",
    "Set Boolean Equality Schemes",
    "Set Contextual Implicit",
    "Set Decidable Equality Schemes",
    "Set Default Timeout",
    "Set Elimination Schemes",
    "Set Extraction AutoInline",
    "Set Extraction KeepSingleton",
    "Set Extraction Optimize",
    "Set Firstorder Depth",
    "Set Hyps Limit",
    "Set Implicit Arguments",
    "Set Ltac Debug",
    "Set Maximal Implicit Insertion",
    "Set Parsing Explicit",
    "Set Printing All",
    "Set Printing Coercion",
    "Set Printing Coercions",
    "Set Printing Depth",
    "Set Printing Existential Instances",
    "Set Printing Implicit",
    "Set Printing Implicit Defensive",
    "Set Printing Matching",
    "Set Printing Notations",
    "Set Printing Synth",
    "Set Printing Universes",
    "Set Printing Width",
    "Set Printing Wildcard",
    "Set Reversible Pattern Implicit",
    "Set Silent",
    "Set Strict Implicit",
    "Set Strongly Strict Implicit",
    "Set Transparent Obligations",
    "Set Virtual Machine",
    "Set Whelp Getter",
    "Set Whelp Server",
    "Show",
    "Show Conjectures",
    "Show Existentials",
    "Show Implicits",
    "Show Intro",
    "Show Intros",
    "Show Obligation Tactic",
    "Show Proof",
    "Show Script",
    "Show Tree",
    "Show XML Proof",
    "Solve Obligations",
    "Strategy",
    "Structure",
    "SubClass",
    "Tactic Definition",
    "Tactic Notation",
    "Test",
    "Test Default Timeout",
    "Test Ltac Debug",
    "Test Printing Depth",
    "Test Printing If for ident",
    "Test Printing Let for ident",
    "Test Printing Matching",
    "Test Printing Synth",
    "Test Printing Width",
    "Test Printing Wildcard",
    "Test Virtual Machine",
    "Test Whelp Getter",
    "Test Whelp Server",
    "Theorem",
    "Time",
    "Timeout",
    "Transparent",
    "Typeclasses eauto",
    "Typeclasses Opaque",
    "Typeclasses Transparent",
    "Undo",
    "Unfocus",
    "Unfocused",
    "Unset",
    "Unset Automatic Coercions Import",
    "Unset Automatic Introduction",
    "Unset Contextual Implicit",
    "Unset Default Timeout",
    "Unset Extraction AutoInline",
    "Unset Extraction KeepSingleton",
    "Unset Extraction Optimize",
    "Unset Hyps Limit",
    "Unset Implicit Arguments",
    "Unset Ltac Debug",
    "Unset Maximal Implicit Insertion",
    "Unset Parsing Explicit",
    "Unset Printing All",
    "Unset Printing Coercion",
    "Unset Printing Coercions",
    "Unset Printing Depth",
    "Unset Printing Existential Instances",
    "Unset Printing Implicit",
    "Unset Printing Implicit Defensive",
    "Unset Printing Matching",
    "Unset Printing Notations",
    "Unset Printing Synth",
    "Unset Printing Universes",
    "Unset Printing Width",
    "Unset Printing Wildcard",
    "Unset Reversible Pattern Implicit",
    "Unset Silent",
    "Unset Strict Implicit",
    "Unset Strongly Strict Implicit",
    "Unset Virtual Machine",
    "Variable",
    "Variables",
    "Whelp Elim",
    "Whelp Hint",
    "Whelp Instance",
    "Whelp Locate",
    "Whelp Match",
    "Write State",
];

var notVernacularWhitelist = [
    "Case",
    "SCase",
    "SSCase",
    "SSSCase",
    "ESD.fsetdec",
    "ESD2.fsetdec",
    "InvBooleans",
    "MonadInv",
    "UseParsingLemmas",
];

function isVernacularCommand(s) {
    var t = coqTrim(s);
    var result = _(vernacularPrefixes).some(function(p) {
        return t.startsWith(p);
    });
    var whitelisted = _(notVernacularWhitelist).some(function(p) {
        return t.startsWith(p);
    });
    if (!result && isUpperCase(t[0]) && !whitelisted) {
        alert("IS THIS A VERNACULAR COMMAND?\n" + s);
    }
    return result;
}

function isProof(s) {
    var t = coqTrim(s);
    return (t.startsWith("Proof.") || t.startsWith("Proof "));
}

var ltacBullets = [
    "{",
    "}",
    "+",
    "-",
    "*",
];

function isLtacBullet(s) {
    var t = coqTrim(s);
    return _(ltacBullets).some(function(p) {
        return t.startsWith(p);
    });
}
