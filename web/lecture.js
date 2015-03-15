var processing = false;
var nbsp = "\u00A0";
var zwsp = "\u200B";
var namesPossiblyInScope = [];

var unicodeList = [
    ("forall", "∀"),
    ("\/", "∨"),
    ("/\\", "∧"),
    ("neg", "¬"),
];

$(document).ready(function() {

    $(window).bind('beforeunload', function(){
        return '⚠⚠⚠ unsaved progress wil be lost ⚠⚠⚠';
    });

    var buttonGroup = $(".btn-group");

    $("<button>", {
        "class": "btn btn-default",
        "id": "prover-down",
    })
        .appendTo(buttonGroup)
        .on("click", function() {
            onCtrlDown();
        })
        .append(mkGlyph("arrow-down"))
    ;

    $("<button>", {
        "class": "btn btn-default",
        "id": "prover-up",
    })
        .appendTo(buttonGroup)
        .on("click", function() {
            onCtrlUp(false);
        })
        .append(mkGlyph("arrow-up"))
    ;

    $("<button>", {
        "class": "btn btn-default",
        "id": "prover-caret",
    })
        .appendTo(buttonGroup)
        .on("click", function() {
            onCtrlEnter();
        })
        .append(mkGlyph("arrow-right"))
        .append(mkGlyph("italic"))
    ;

    // $("<button>", {
    //     "class": "btn btn-success",
    //     "html": $("<span>")
    //         .append(mkGlyph("tree-deciduous"))
    //         //.append(nbsp + "Proof Tree")
    //     ,
    //     "id": "prooftree-button",
    // })
    //     .appendTo(buttonGroup)
    //     .on("click", function() {
    //         asyncLog("MANUALENTERPROOFTREE");
    //         enterProofTree();
    //     })
    //     .attr("disabled", true)
    // ;

    // $("<button>", {
    //     "class": "btn btn-danger",
    //     "html": $("<span>")
    //         .append(mkGlyph("fire"))
    //         //.append(nbsp + "Abort Proof Tree")
    //     ,
    //     "id": "noprooftree-button",
    // })
    //     .appendTo(buttonGroup)
    //     .css("display", "none")
    // ;

    $("<button>", {
        "class": "btn btn-default",
        "html": $("<span>")
            .append(mkGlyph("eye-open"))
            //.append(nbsp + "Peek at Editor")
        ,
        "id": "peek-button",
    })
        .appendTo(buttonGroup)
        .css("display", "none")
        .on("click", peekAtEditorUI)
    ;

    $("<button>", {
        "class": "btn btn-default",
        "html": $("<span>")
            .append(mkGlyph("eye-close"))
            //.append(nbsp + "Return to Proof Tree")
        ,
        "id": "unpeek-button",
    })
        .appendTo(buttonGroup)
        .css("display", "none")
        .on("click", unpeekAtEditorUI)
    ;

    /* Temporarily disabled
    $("<button>", {
        "class": "btn btn-default",
        "html": $("<span>")
            .append(mkGlyph("cloud-download"))
            .append(nbsp + "Load remotely")
        ,
        "id": "load-remote-button",
    })
        .appendTo(buttonGroup)
        .on("click", loadRemote)
    ;

    $("<button>", {
        "class": "btn btn-default",
        "html": $("<span>")
            .append(mkGlyph("cloud-upload"))
            .append(nbsp + "Save remotely")
        ,
        "id": "save-remote-button",
    })
        .appendTo(buttonGroup)
        .on("click", function() { alert("TODO"); })
    ;
    */

    $("#filepicker").on("change", function() {
        // TODO: warning about resetting Coq/saving file
        loadFile();
        $(this).val(""); // forces change when same file is picked
    })

    $("<button>", {
        "class": "btn btn-default",
        "html": $("<span>")
            .append(mkGlyph("floppy-open"))
            .append(nbsp + nbsp + "Load")
        ,
        "id": "load-local-button",
    })
        .appendTo(buttonGroup)
        .on("click", loadLocal)
    ;

    var saveLocalButton = $("<button>", {
        "class": "btn btn-default",
        "id": "save-local-button",
        "html": $("<span>")
            .append(mkGlyph("floppy-save"))
            .append(nbsp + nbsp + "Save"),
    })
        .appendTo(buttonGroup)
        .on("click", saveLocal)
    ;

    $("<button>", {
        "class": "btn btn-info",
        "data-target": "feedback",
        "data-toggle": "modal",
        "id": "feedback-button",
        "html": $("<span>")
            .append(mkGlyph("bullhorn"))
            //.append(nbsp + nbsp + "Feedback"),
    })
        .appendTo(buttonGroup)
        .on("click", function() {
            $("#feedback").modal();
        })
    ;

    $("#feedback").on('shown.bs.modal', function () {
        $("#feedback-form").focus();
    });

    $("#submit-feedback").on("click", function() {
        var feedback = $("#feedback-form").text();
        $("#feedback-form").text("");
        asyncLog("FEEDBACK " + feedback);
        $("#cancel-feedback").click();
    });

    $("<button>", {
        "class": "btn btn-default",
        "data-target": "help",
        "data-toggle": "modal",
        "id": "feedback-button",
        "html": $("<span>")
            .append(mkGlyph("question-sign"))
            //.append(nbsp + nbsp + "Help"),
    })
        .appendTo(buttonGroup)
        .on("click", function() {
            $("#help").modal();
        })
    ;

    $("<button>", {
        "class": "btn btn-default",
        "data-target": "help",
        "data-toggle": "modal",
        "id": "options-button",
        "html": $("<span>")
            .append(mkGlyph("th-list"))
            //.append(nbsp + nbsp + ""),
    })
        .appendTo(buttonGroup)
        .on("click", function() {
            $("#options").modal();
        })
    ;

    $("#set-printing-all").change(function() {
        if($(this).is(":checked")) {
            asyncRequest('setprintingall', undefined);
        } else {
            asyncRequest('unsetprintingall', undefined);
        }
    });

    $("<button>", {
        "class": "btn btn-default",
        "html": '<img src="media/ajax-loader.gif" />',
        "id": "loading",
    })
        .appendTo(buttonGroup)
        .css("padding", "2px 10px")
        .css("display", "none")
    ;

    $("<a>", {
        "download": "output.v",
        "id": "save-local-link",
    })
        .css("display", "none")
        .appendTo(buttonGroup)
    ;

    //resize();
    $(window).resize(resize);

    $("body")
        .on("keydown", globalKeyHandler)
    ;

    asyncRevision()
        .then(function(response) {
            $("#revision").html(
                "Server revision: " + response.rResponse.contents[0]
                    + "<br/>Client revision: " + response.rResponse.contents[1]
            );
            return asyncResetCoq();
        })
        .then(function() {
            $("#editor").focus();
        })
        .catch(outputError)
    ;

});

function loadFile() {
    var file = $("#filepicker")[0].files[0];
    $("#save-local-link").attr(
        "download",
        // remove versioning number
        file.name.replace(/ \(\d+\)/g, '')
    );
    var reader = new FileReader();
    reader.onload = function(e) {
        onLoad(reader.result);
    }
    reader.readAsText(file);
}

function resize() {
    var windowHeight = $(window).height();
    // careful, there are many <body> when using proof tree!
    //$("html > body").height(windowHeight);
    //var height = windowHeight - $("#toolbar").height();
    //height = Math.floor(height / 2);
    //$("#editor").css("height", height);
    //$("#coqtop").css("height", height);
    //$("#prooftree").css("height", height);
    //$("#pt-1").css("height", height);
    //$("svg").css("height", height);
    // TODO: fix height bug
    var width = $(window).width();
    var height = $("#prooftree").height();
    if (activeProofTree !== undefined) {
        activeProofTree.resize($(window).width(), height);
    }
}

function onLoad(text) {

    asyncLog("LOAD " + text);

    $("#editor").empty();//.css("display", "");
    $("#coqtop").empty();//.css("display", "");
    $("#prooftree").empty();//.css("display", "none");
    activeProofTree = undefined;

    resetEditor(text);

    switchToEditorUI();

    asyncResetCoq()
        .then(function() {
            cm.focus();
        })
        .catch(outputError);

}

// Some of this code has been borrowed from the ProofWeb project
// Their license is unclear, TODO make sure we can borrow, oops!
var delimiters = ['.'];
function my_index(str) {
    var index = +Infinity;
    _(delimiters).each(function(delimiter) {
        var pos = str.indexOf(delimiter);
        if (pos >= 0 && pos < index) { index = pos; }
    });
    if (index !== +Infinity) { return index; }
    else { return -1; }
}

var bullets = ["{", "}", "+", "-", "*"];

function next(str) {
    // if the very next thing is one of {, }, +, -, *, it is the next
    var trimmed = coqTrimLeft(str);
    if (_(bullets).contains(trimmed[0])) {
        return str.length - trimmed.length + 1;
    }
    // otherwise, gotta find a dot
    return coq_find_dot(coq_undot(str), 0) + 1;
}

function prev(str) {
    // remove the last delimiter, since we are looking for the previous one
    var str = str.substring(0, str.length - 1);
    // if the very last thing is one of {, }, +, -, *, it is the prev
    var trimmed = coqTrimRight(str);
    if (_(bullets).contains(trimmed[trimmed.length - 1])) {
        return trimmed.length;
    }
    // otherwise, find the last dot
    return coq_find_last_dot(coq_undot(str), 0) + 1;
}

function count (str, pat) {
    var arr = str.split (pat);
    return (arr.length);
}

// highlight dot that are terminators as opposed to the others
function coq_undot(str) {
    str = str.replace(/[.][.][.]/g, '__.'); // emphasize the last dot of ...
    str = str.replace(/[.][.]/g, '__'); // hides .. in notations
    str = str.replace(/[.][a-zA-Z1-9_]/g, '__'); // hides qualified identifiers
    // hide curly braces that are implicit arguments
    str = str.replace(/\{((?:[^\.\}]|\.(?!\s))*)\}/g, "_$1_");
    // make other braces look like periods
    str = str.replace(/[\{\}]/g, ".");
    return str;
}

function coq_find_dot(str, toclose) {
    var index = my_index(str);
    if (index == -1) { return index; }
    var tocheck = str.substring(0, index);
    var opened = count(tocheck, "(*") + toclose - count(tocheck, "*)");
    if (opened <= 0) {
        return index;
    } else {
        var newindex = coq_find_dot(str.substring(index + 1), opened);
        if (newindex == -1) return -1;
        return index + newindex + 1;
    }
}

function coq_get_last_dot(str) {
    var modified = str;
    var index = -1;
    while (my_index(modified) >= 0) {
        index = my_index(modified);
        modified = modified.substring(0, index) + " " +
            modified.substring(index + 1);
    }
    return index;
}

function coq_find_last_dot (str, toopen) {
    var index = coq_get_last_dot(str);
    if (index == -1) { return index; }
    var tocheck = str.substring(index + 1);
    var closed = count(tocheck, "*)") + toopen - count(tocheck, "(*");
    if (closed <= 0) {
        return index;
    } else {
        var newindex = coq_find_last_dot(str.substring(0, index), closed);
        return newindex;
    }
}

function globalKeyHandler(evt) {
    //console.log(evt.keyCode);
    if (evt.ctrlKey) {
        switch(evt.keyCode) {
        case 76: // Ctrl-L
            $("#load-local-button").click();
            evt.preventDefault();
            break;
        default:
            break;
        };
    }
}

var goingDown = true, goingUp = false;

function updateCoqtopPane(direction, response) {

    var contents = response.rResponse.contents;

    switch (typeof contents) {
    case "string": break;
    case "object":
        if (contents.length > 1) {
            alert("Found contents with length greater than 1, see log");
            console.log(contents);
        }
        contents = contents[0];
        break;
    default:
        alert("Found contents with type different than string and object, see log");
        console.log(typeof contents, contents);
    };
    contents = contents.trim();

    switch (response.rResponse.tag) {
    case "Good":
        $("#coqtop")
            .toggleClass("alert-success", true)
        ;
        $("#coqtop").empty();
        $("#coqtop-error").empty();
        var contextDiv = $("<div>", { "id": "context" }).appendTo("#coqtop");
        var subgoalsDiv = $("<div>", {
            "id": "subgoals",
        })
            .css("margin-top", "10px")
            .appendTo("#coqtop")
        ;
        var contentsDiv = $("<div>", {
            "id": "contents",
        })
            .css("margin-top", "10px")
            .appendTo("#coqtop")
        ;

        var nbFocused = response.rGoals.focused.length;
        var unfocused = response.rGoals.unfocused[0];

        if (nbFocused > 0) {
            _(response.rGoals.focused[0].gHyps).each(function(h) {
                contextDiv.append(PT.showHypothesis(extractHypothesis(h)) + "\n");
            });
            contextDiv.append($("<hr>").css("border", "1px solid black"));
            contextDiv.append(showTerm(extractGoal(response.rGoals.focused[0].gGoal)));

            var nbUnfocused = (unfocused === undefined)
                ? 0
                : unfocused[0].length + unfocused[1].length
            ;
            if (nbUnfocused === 0) {
                subgoalsDiv.text(
                    nbFocused + " subgoal" + (nbFocused <= 1 ? "" : "s")
                );
            } else {
                subgoalsDiv.text(
                    nbFocused + " focused subgoal" + (nbFocused <= 1 ? "" : "s")
                        + ", " + nbUnfocused + " unfocused"
                );
            }

            contentsDiv.text(contents);

        } else if (unfocused !== undefined) {

            var nbRemaining = unfocused[0].length + unfocused[1].length;

            subgoalsDiv.text(
                nbRemaining + " remaining subgoal" + (nbRemaining <= 1 ? "" : "s")
            );

        } else {

            $("#prooftree-button").attr("disabled", true);

            contents = stripWarning(contents);

            // postprocessing of Inductive
            if (contents.startsWith("Inductive")) {
                contents = contents
                    .replace(/:=\s+/, ":=\n| ")
                    .replace(/ \| /, "\n| ")
                ;
            }

            contentsDiv.html(contents);

        }

        // if we use highlightBlock here, it fails, so use the core highlighting
        //var contentsText = $("#contents").text();
        //var textHl = hljs.highlight('ocaml', contentsText, true).value;
        //$("#contents").html(textHl);

        break;
    case "Fail":
        // maybe still display the goal?
        $("#coqtop-error").empty().text(stripWarning(contents));
        break;
    };

    /*
    // also, enable/disable the button depending on whether we are in proof mode
    asyncStatus()
        .then(function(status) {

            // while at it, let's gather names of definitions for proof purposes
            // TODO: should this be done by prooftree.js?
            if (status.current !== null && !_(namesPossiblyInScope).contains(status.current)) {
                namesPossiblyInScope.push(status.current);
            }

            $("#prooftree-button").attr("disabled", !status.proving);
            if (status.proving) {
                // automatically enter proof mode if not in the process of proving more things
                var lastCommand = getLastProved();
                if (_(lastCommand).contains("(* notree *)")) {
                    asyncLog("NOTREE");
                }
                if (direction === goingDown
                    && ! lastCommand.endsWith("Proof.")
                    && !_(lastCommand).contains("(* notree *)")
                    && $("#provwill").text().length === 0) {
                    if (!processing) {
                        asyncLog("AUTOENTERPROOFTREE");
                        enterProofTree();
                    }
                }
            }

        })
    ;
    */

}

function undoCallback(fromTree, undone, response) {
    switch(response.rResponse.tag) {
    case "Good":
        if (activeProofTree !== undefined) {
            activeProofTree.onUndo(undone, response);
        }
        var stepsToRewind = + response.rResponse.contents[0];
        console.log("Rewinding additional " + stepsToRewind + " steps");
        while (stepsToRewind-- > 0) {
            var rProved = mProved.find();
            var rUnlocked = mUnlocked.find();
            var proved = doc.getRange(rProved.from, rProved.to);
            if (proved === "") { return; }
            var prevIndex = prev(proved);
            var pieceUnproved = proved.substring(prevIndex);
            if (pieceUnproved === "") { return; }
            var prevPos = cm.findPosH(rProved.from, prevIndex, "char");
            markProved(rProved.from, prevPos);
            markProving(prevPos, prevPos);
            markToprove(prevPos, prevPos);
            markUnlocked(prevPos, rUnlocked.to);
            if (!fromTree) { doc.setCursor(prevPos); }
        }
        response.rResponse.contents[0] = ""; // don't show the user the steps number
        break;
    };
    updateCoqtopPane(goingUp, response);
}

/*
  Returns the position of the caret w.r.t. the editor: this includes all the
  characters in #proved, #proving, #provwill and #unlocked
*/
function getCaretPos() {
    var sel = rangy.getSelection();
    var rng = rangy.createRange();
    rng.selectNodeContents($("#editor")[0]);
    rng.setEnd(sel.focusNode, sel.focusOffset);
    return rng.toString().length;
}

var safeDelimiters = [' ', '\n'];

/*
 * Adds [command] to [provwill], making sure that it is separated from the
 * previous text. Returns how many characters were added for safety.
 */
/*
function safeAppendToProvwill(command) {
    var returnValue = 0;
    // if the command does not start with a space, and the last thing did not
    // end with a newline or space, let's make some room
    var stringBefore = proved + proving + provwill;
    if (stringBefore !== '') {
        var characterBefore = stringBefore[stringBefore.length - 1];
        var characterAfter = command[0];
        if (!_(safeDelimiters).contains(characterBefore)
            && !_(safeDelimiters).contains(characterAfter)) {
            appendToProvwill(' ');
            returnValue = 1;
        }
    }
    appendToProvwill(command);
    return returnValue;
}
*/

/*
 * Prepends [command] to [provwill], making sure that it is separated from the
 * previous text and the next text. Returns how many characters were added for
 * safety.
 */
function safePrependToprove(command) {

    var returnValue = 0;

    // if the command does not start with a space, and the last thing did not
    // end with a newline or space, let's make some room
    var stringBefore = getProved() + getProving();
    if (stringBefore !== "") {
        var characterBefore = stringBefore[stringBefore.length - 1];
        var characterAfter = command[0];
        if (!_(safeDelimiters).contains(characterBefore)
            && !_(safeDelimiters).contains(characterAfter)) {
            command = ' ' + command;
            returnValue++;
        }
    }

    // if the command does not end with a space, and the next thing does not
    // start with a newline or space, let's make some room
    var stringAfter = getToprove() + getUnlocked();
    if (stringAfter !== "") {
        var characterBefore = command[command.length - 1];
        var characterAfter = stringAfter[0];
        if (!_(safeDelimiters).contains(characterBefore)
            && !_(safeDelimiters).contains(characterAfter)) {
            var rUnlocked = mUnlocked.find();
            doc.replaceRange(" ", rUnlocked.from);
            returnValue++;
        }
    }

    var rProving = mProving.find();
    var rToprove = mToprove.find();
    var rUnlocked = mUnlocked.find();
    mToprove.inclusiveLeft = false;
    doc.replaceRange(command, rToprove.from);
    mToprove.inclusiveLeft = true;
    markToprove(rProving.to, rUnlocked.from);
    // if rToprove was empty, the last command actually inserted into unlocked
    if (getToprove() === "") {
        var rUnlocked = mUnlocked.find();
        var newPos = cm.findPosH(rUnlocked.from, command.length, "char");
        markToprove(rToprove.from, newPos);
        markUnlocked(newPos, rUnlocked.to);
    }

    return returnValue;
}

function mkGlyph(name) {
    return $("<i>", {
        "class": "glyphicon glyphicon-" + name,
    });
}

function insertAtSelection(txt) {
    var sel, newrange;
    sel = rangy.getSelection();
    if (sel.rangeCount > 0) {
        newrange = insertText(txt, sel.getRangeAt(0));
        sel.setSingleRange(newrange);
    }
}

function insertText(txt, inrange) {
    var range = inrange.cloneRange();
    var tn = document.createTextNode(txt);
    range.insertNode(tn);
    range.selectNode(tn);
    range.normalizeBoundaries();
    range.collapse(false);
    return range;
}

function getCaretVerticalPosition() {
    var sel = rangy.getSelection();
    var range = sel.getRangeAt(0).cloneRange();
    var span = $("<span>", { "id": "toremove", "text": " " })[0];
    range.insertNode(span);
    var caretTop = span.getBoundingClientRect().top;
    span.remove();
    return caretTop;
}

function peekAtEditorUI() {

    $("#main").height("100%");
    $("#prooftree").height("0%");
    $("#coqtop").css("display", "");
    $("#coqtop-error").height("20%");

    $("#peek-button").css("display", "none");
    $("#unpeek-button").css("display", "");
    $("#editor").focus();

}

function unpeekAtEditorUI() {

    $("#main").height("20%");
    $("#prooftree").height("80%");
    $("#coqtop").css("display", "none");
    $("#coqtop-error").height("100%");

    $("#peek-button").css("display", "");
    $("#unpeek-button").css("display", "none");
    $("#prooftree").focus();

    activeProofTree.update();

}

function switchToProofUI() {

    $("#main").height("20%");
    $("#prooftree").height("80%");
    $("#coqtop").css("display", "none");
    $("#coqtop-error").height("100%");

    $("#prooftree-button").css("display", "none");
    $("#noprooftree-button").css("display", "");
    $("#peek-button").css("display", "");

}

function switchToEditorUI() {

    $("#main").height("100%");
    $("#prooftree").height("0%");
    $("#coqtop").css("display", "");
    $("#coqtop-error").height("20%");

    $("#prooftree-button").css("display", "");
    $("#noprooftree-button").css("display", "none");
    $("#peek-button").css("display", "none");
    $("#unpeek-button").css("display", "none");

}

function enterProofTree() {
    // do this as early as possible to avoid races
    switchToProofUI();
    proofTreeQueryWish('Proof.');
}

function createProofTree(response) {

    activeProofTree = new ProofTree(
        $("#prooftree")[0],
        $(window).width(),
        $("#prooftree").height(),
        onQed,
        function() { $("#loading").css("display", ""); },
        function() { $("#loading").css("display", "none"); }
    );

    // TODO: this is so ugly, find a different way
    /*
      need to figure out what the statement of the theorem is, and
      there seems to be no way to ask that with status, so look it up in
      the proved region as the last statement
    */
    var proved = $("#proved").text();
    var assertionKeywords = [
        "Theorem", "Lemma", "Remark", "Fact", "Corollary", "Proposition"
    ];
    // lookup the last time an assertion keyword was proved
    var position = _(assertionKeywords)
        .map(function(keyword) {
            return proved.lastIndexOf(keyword);
        })
        .max()
        .value()
    ;
    var theoremStatement = proved.substring(position);
    // get rid of anything after the statement, like "Proof."
    theoremStatement = theoremStatement.substring(0, next(theoremStatement));

    activeProofTree.newAlreadyStartedTheorem(
        theoremStatement,
        response,
        lectureTactics
    );

}

function exitProofTree() {

    switchToEditorUI();

    $("#prooftree").empty();
    activeProofTree = undefined;

    $("#editor").focus();

    asyncLog("EXITPROOFTREE");

}

function getLastProved() {
    var proved = $("#proved").text();
    return coqTrim(proved.substring(prev(proved)));
}

/*
 * TODO: now that ProofTree does not undo, no need to backtract and redo.
 * However, we now need to insert the 'Proof.' keyword.
 */
function onQed(prooftree) {

    switchToEditorUI();

    var unlocked = pweGetUnlocked();
    pweSetUnlocked('\nQed.' + unlocked);
    proverDown();

    $("#prooftree").empty();
    activeProofTree = undefined; // bad attempt at GC?
    repositionCaret();

}

function stripWarning(s) {
    return s.replace(/^Warning: query commands should not be inserted in scripts\n/g, "");
}

function loadRemote() {

    var html = $("<div>");

    asyncListLectures(function(response) {
        var files = response.rResponse.contents;

        var fileList = $("<select>", {
            "class": "form-control",
            "id": "lecture-select",
            "width": "200px",
        }).appendTo(html);
        _(files).each(function(file) {
            fileList.append(
                $("<option>", {
                    "value": file,
                    "html": file,
                })
            );
        });

        $("<button>", {
            "text": "Load",
        })
            .appendTo(html)
            .on("click", function() {
                var fileToLoad = $("#lecture-select").val();
                $("#load-remote-button").popover("destroy");
                asyncLoadLecture(fileToLoad, function(response) {
                    onLoad(response.rResponse.contents[0]);
                });
            })
        ;

        $("<button>", {
            "text": "Cancel",
        })
            .appendTo(html)
            .on("click", function() {
                $("#load-remote-button").popover("destroy");
            })
        ;

        $("#load-remote-button")
            .popover({
                "content": html,
                "html": true,
                "placement": "bottom",
            })
            .popover("show");

    });

}

function loadLocal() {

    $("#filepicker").click();

}

function saveLocal() {

    var text = doc.getValue();
    var blob = new Blob([text], {type:'text/plain;charset=UTF-8'});
    var url = window.URL.createObjectURL(blob);
    $("#save-local-link").attr("href", url);
    $("#save-local-link")[0].click();
    cm.focus();

}

if (!String.prototype.startsWith) {
    Object.defineProperty(String.prototype, 'startsWith', {
        enumerable: false,
        configurable: false,
        writable: false,
        value: function(searchString, position) {
            position = position || 0;
            return this.lastIndexOf(searchString, position) === position;
        }
    });
}

if (!String.prototype.endsWith) {
    Object.defineProperty(String.prototype, 'endsWith', {
        value: function(searchString, position) {
            var subjectString = this.toString();
            if (position === undefined || position > subjectString.length) {
                position = subjectString.length;
            }
            position -= searchString.length;
            var lastIndex = subjectString.indexOf(searchString, position);
            return lastIndex !== -1 && lastIndex === position;
        }
    });
}

function unquote_str (oldstr) {
    var str = oldstr
        .replace(/&lt;/g, "<")
        .replace(/&gt;/g, ">")
        .replace(/&quot;/g, "\"")
        .replace(/&apos;/g, "'")
        .replace(/&amp;/g, "&")
        .replace(/<br>/g,"\n")
        .replace(/<BR>/g,"\n")
        .replace(/<BR\/>/g,"\n")
    ;
    return str;
}

function makeGroup(name, tactics) {
    return {
        "name": name,
        "tactics": _(tactics).map(function(s) { return s + '.'; }).value(),
    };
}

function lectureTactics(pt) {

    var curGoal = (isGoal(this.curNode)) ? this.curNode : this.curNode.parent;
    var curHyps = _(curGoal.hyps).map(function(h) { return h.hName; }).reverse();
    var curNames = _(curHyps).union(namesPossiblyInScope.reverse());

    var res = [

        makeGroup(
            "terminators",
            ["reflexivity", "discriminate", "assumption", "eassumption",]
        ),

        makeGroup(
            "autos",
            ["auto", "eauto"]
        ),

        makeGroup(
            "introductions",
            ["intro", "intros"]
        ),

        makeGroup(
            "break_if, f_equal, subst",
            ["break_if", "f_equal", "repeat f_equal", "subst"]
        ),

        makeGroup(
            "simplifications",
            ["simpl"].concat(
                _(curHyps).map(function(h) { return "simpl in " + h; }).value()
            ).concat(["simpl in *"])
        ),

        makeGroup(
            "constructors",
            ["left", "right", "split", "constructor", "econstructor", "eexists"]
        ),

        makeGroup(
            "destructors",
            _(curHyps).map(function(h) { return "destruct " + h; }).value()
        ),

        makeGroup(
            "inductions",
            _(curHyps).map(function(h) { return "induction " + h; }).value()
        ),

        makeGroup(
            "inversions",
            _(curHyps).map(function(h) { return "inversion " + h; }).value()
        ),

        makeGroup(
            "solvers",
            ["congruence", "omega", "firstorder"]
        ),

        makeGroup(
            "applications",
            _(curNames).map(function(n) { return "apply " + n; }).value()
                .concat(
                    _(curNames).map(function(n) { return "eapply " + n; }).value()
                )
        ),

        makeGroup(
            "rewrites",
            _(curNames).map(function(n) { return "rewrite -> " + n; }).value()
                .concat(
                    _(curNames).map(function(n) { return "rewrite <- " + n; }).value()
                )
        ),

        makeGroup(
            "applications in",
            _(curNames).map(function(n) {
                return _(curHyps)
                    .map(function(h) {
                        if (h === n) { return []; }
                        return ([
                            "apply " + n + " in " + h,
                            "eapply " + n + " in " + h
                        ]);
                    })
                    .flatten(true).value();
            }).flatten(true).value()
        ),

        makeGroup(
            "rewrites in",
            _(curNames).map(function(n) {
                return _(curHyps)
                    .map(function(h) {
                        if (h === n) { return []; }
                        return ([
                            ("rewrite -> " + n + " in " + h),
                            ("rewrite <- " + n + " in " + h)
                        ]);
                    })
                    .flatten(true).value()
                ;
            }).flatten(true).value()
        ),

        makeGroup(
            "reverts",
            _(curHyps).map(function(h) { return "revert " + h; }).value()
        ),

    ];

    return (
        _(res)
            .map(function(elt) {
                if ($.type(elt) === "string") {
                    return elt + ".";
                } else {
                    return elt;
                }
            })
            .value()
    );

}

/*
 * For the following callbacks, the assumption is that they may be triggered
 * either as a response from the editor asking for some request to be performed,
 * or from the proof tree asking for some request to be performed. As a result,
 * things that should happen only in one of these cases should be done before
 * the request is sent. For instance:
 * - when the editor asks for a command to be performed, it should clear it from
 *   the unlocked area, as this does not happen for commands sent from the proof
 *   tree mode ;
 * - that's all I can think of right now...
 */

function editorOnRequestTriggered(requestType, request) {
    switch (requestType) {
    case 'query':
/*
        var index = next(provwill);
        var nextProvwill = provwill.substring(0, index);
        if (nextProvwill.trim() !== request.trim()) {
            console.log(
                'request triggered was', request,
                'but was expecting', nextProvwill
            );
        }
        console.log('AND THERE');
        setProving(nextProvwill);
        console.log('AND THERE');
        truncateProvwillFromIndex(index);
        console.log('AND THERE');
        break;
*/
    }
}

function editorOnResponse(requestType, request, response) {
    switch (requestType) {
    case 'query':
        switch(response.rResponse.tag) {

        case 'Good':
            var rProving = mProving.find();
            var proving = doc.getRange(rProving.from, rProving.to);
            if (coqTrim(proving) !== coqTrim(request)) {
                console.log(
                    'request response was for', request,
                    'but was expecting for', proving
                );
                return;
            }
            var rProved = mProved.find();
            var nextPos = rProving.to;
            markProved(rProved.from, nextPos);
            markProving(nextPos, rProving.to);
            doc.setCursor(nextPos);
            updateCoqtopPane(goingDown, response);

            if (activeProofTree === undefined) {
                if (coqTrim(request) === 'Proof.') {
                    createProofTree(response);
                } else {
                    // used to do asyncStatus here and check stauts.proving here
                    // but I'd rather avoid a request...  if you do async
                    // operations here, you need to fix [processingAsyncRequest]
                    if (response.rGoals.focused.length === 1 ) {
                        enterProofTree();
                    }
                }
            } else {

            }

            break;

        case 'Fail':
            // move proving and toprove back to unlocked
            var rProving = mProving.find();
            var rProved = mProved.find();
            var rUnlocked = mUnlocked.find();
            markProving(rProving.from, rProving.from);
            markToprove(rProving.from, rProving.from);
            markUnlocked(rProving.from, rUnlocked.to);
            doc.setCursor(rUnlocked.from);
            updateCoqtopPane(goingDown, response);
            break;
        };
        break;

    }
}

/*
 * If [request] is the next thing in the provwill or unlocked region, instead of
 * adding the [request] to [provwill], we will shift the incoming one instead.
 * Returns [true] if it did that.
 */
function lookupRequestInIncoming(request) {

    var rProving = mProving.find();
    var proving = doc.getRange(rProving.from, rProving.to);

    if (proving !== "") {
        // this branch happens when one processes a lot of commands
        return sameTrimmed(proving, request);
    }

    var rToprove = mToprove.find();
    var toprove = doc.getRange(rToprove.from, rToprove.to);

    if (toprove !== "") {
        var nextIndex = next(toprove);
        var nextItem = toprove.substring(0, nextIndex);
        return sameTrimmed(nextItem, request);
    }

    var rUnlocked = mUnlocked.find();
    var unlocked = doc.getRange(rUnlocked.from, rUnlocked.to);
    var nextIndex = next(unlocked);
    var nextUnlocked = unlocked.substring(0, nextIndex);
    var nextPos = cm.findPosH(rUnlocked.from, nextIndex, "char");

    if (!sameTrimmed(nextUnlocked, request)) {
        return false;
    }

    markToprove(rToprove.from, nextPos);
    markUnlocked(nextPos, rUnlocked.to);

    return true;

}

function proofTreeQueryWish(request) {

    var requestWasPresent = lookupRequestInIncoming(request);

    if (requestWasPresent) {
        //console.log("Found");
    } else {
        //console.log("NOT Found");
    }

    if (!requestWasPresent) {
        switch (request) {
        case '{':
        case '}':
            safePrependToprove(request);
            break;
            // for these, I want to put a newline
        case 'Proof.':
        case 'Qed.':
            safePrependToprove('\n' + request);
            break;
        default:
            safePrependToprove(request);
            //safePrependToprove('\n' + request);
            break;
        }
    }

    processToprove();

}

// TODO: support nested comments?

function coqTrim(s) {
    return s
    // remove comments first
        .replace(/\(\*[\s\S]*?\*\)/g, '')
    // then trim
        .replace(/^[\s\uFEFF\xA0]+|[\s\uFEFF\xA0]+$/g, '')
    ;
}

function coqTrimLeft(s) {
    return s
    // remove one heading comment first
        .replace(/^[\s\uFEFF\xA0]+\(\*[\s\S]*?\*\)/g, '')
    // then trim left
        .replace(/^[\s\uFEFF\xA0]+/g, '')
    ;
}

function coqTrimRight(s) {
    return s
        .replace(/[\s\uFEFF\xA0]+$/g, '')
    ;
}

function sameTrimmed(a, b) {
    return (coqTrim(a) === coqTrim(b));
}
