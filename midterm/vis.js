// Custom Sterling visualization for file-system.frg.
// Renders each State as a tree plus a compact transition summary.

(function renderFileSystemTrace() {
  div.innerHTML = "";
  div.style.overflow = "auto";
  div.style.padding = "10px";

  function tuplesOf(rel) {
    if (!rel || typeof rel.tuples !== "function") {
      return [];
    }
    return rel.tuples();
  }

  function atomName(atom) {
    return atom ? atom.toString() : "";
  }

  function sortedNames(values) {
    return Array.from(values).sort(function (a, b) {
      return a.localeCompare(b, undefined, { numeric: true, sensitivity: "base" });
    });
  }

  function toNameSet(rel) {
    var out = new Set();
    var tuples = tuplesOf(rel);
    for (var i = 0; i < tuples.length; i++) {
      var atoms = tuples[i]._atoms || [];
      if (atoms.length >= 1) {
        out.add(atomName(atoms[0]));
      }
    }
    return out;
  }

  var stateRel = typeof State !== "undefined" ? State : null;
  var fileRel = typeof File !== "undefined" ? File : null;
  var dirRel = typeof Dir !== "undefined" ? Dir : null;
  var liveRel = typeof live !== "undefined" ? live : null;
  var parentRel = typeof parent !== "undefined" ? parent : null;
  var rootRel = typeof root !== "undefined" ? root : null;
  var nextRel = typeof next !== "undefined" ? next : null;

  if (!stateRel) {
    div.textContent = "No State relation found in this instance.";
    return;
  }

  var fileSet = toNameSet(fileRel);
  var dirSet = toNameSet(dirRel);

  var stateSet = toNameSet(stateRel);
  var states = sortedNames(stateSet);

  var liveByState = new Map();
  var parentByState = new Map();
  var rootByState = new Map();
  var nextByState = new Map();
  var predCount = new Map();

  var liveTuples = tuplesOf(liveRel);
  for (var iLive = 0; iLive < liveTuples.length; iLive++) {
    var liveAtoms = liveTuples[iLive]._atoms || [];
    if (liveAtoms.length < 3) {
      continue;
    }
    var liveState = atomName(liveAtoms[0]);
    var liveObj = atomName(liveAtoms[1]);
    if (!liveByState.has(liveState)) {
      liveByState.set(liveState, new Set());
    }
    liveByState.get(liveState).add(liveObj);
  }

  var parentTuples = tuplesOf(parentRel);
  for (var iParent = 0; iParent < parentTuples.length; iParent++) {
    var parentAtoms = parentTuples[iParent]._atoms || [];
    if (parentAtoms.length < 3) {
      continue;
    }
    var parentState = atomName(parentAtoms[0]);
    var childObj = atomName(parentAtoms[1]);
    var parentObj = atomName(parentAtoms[2]);
    if (!parentByState.has(parentState)) {
      parentByState.set(parentState, new Map());
    }
    parentByState.get(parentState).set(childObj, parentObj);
  }

  var rootTuples = tuplesOf(rootRel);
  for (var iRoot = 0; iRoot < rootTuples.length; iRoot++) {
    var rootAtoms = rootTuples[iRoot]._atoms || [];
    if (rootAtoms.length < 2) {
      continue;
    }
    rootByState.set(atomName(rootAtoms[0]), atomName(rootAtoms[1]));
  }

  var nextTuples = tuplesOf(nextRel);
  for (var iNext = 0; iNext < nextTuples.length; iNext++) {
    var nextAtoms = nextTuples[iNext]._atoms || [];
    if (nextAtoms.length < 2) {
      continue;
    }
    var fromState = atomName(nextAtoms[0]);
    var toState = atomName(nextAtoms[1]);
    nextByState.set(fromState, toState);
    predCount.set(toState, (predCount.get(toState) || 0) + 1);
  }

  function stateOrder() {
    if (states.length === 0) {
      return [];
    }
    var starts = [];
    for (var i = 0; i < states.length; i++) {
      if (!predCount.has(states[i])) {
        starts.push(states[i]);
      }
    }
    starts = sortedNames(starts);
    var first = starts.length > 0 ? starts[0] : states[0];
    var ordered = [];
    var seen = new Set();
    var cursor = first;
    while (cursor && !seen.has(cursor)) {
      ordered.push(cursor);
      seen.add(cursor);
      cursor = nextByState.get(cursor);
    }
    var leftovers = states.filter(function (s) {
      return !seen.has(s);
    });
    leftovers = sortedNames(leftovers);
    for (var j = 0; j < leftovers.length; j++) {
      ordered.push(leftovers[j]);
    }
    return ordered;
  }

  function objectTag(objName) {
    if (dirSet.has(objName)) {
      return "[D]";
    }
    if (fileSet.has(objName)) {
      return "[F]";
    }
    return "[O]";
  }

  function objectCompare(a, b) {
    var aDir = dirSet.has(a);
    var bDir = dirSet.has(b);
    if (aDir !== bDir) {
      return aDir ? -1 : 1;
    }
    return a.localeCompare(b, undefined, { numeric: true, sensitivity: "base" });
  }

  function childrenByParent(liveSet, parentMap) {
    var childMap = new Map();
    var entries = Array.from(parentMap.entries());
    for (var i = 0; i < entries.length; i++) {
      var child = entries[i][0];
      var par = entries[i][1];
      if (!liveSet.has(child) || !liveSet.has(par)) {
        continue;
      }
      if (!childMap.has(par)) {
        childMap.set(par, []);
      }
      childMap.get(par).push(child);
    }
    var keys = Array.from(childMap.keys());
    for (var j = 0; j < keys.length; j++) {
      childMap.get(keys[j]).sort(objectCompare);
    }
    return childMap;
  }

  function renderTree(stateName) {
    var liveSet = liveByState.get(stateName) || new Set();
    var parentMap = parentByState.get(stateName) || new Map();
    var rootObj = rootByState.get(stateName) || null;
    var childMap = childrenByParent(liveSet, parentMap);
    var lines = [];
    var seen = new Set();

    function walk(node, depth, path) {
      var indent = "  ".repeat(depth);
      lines.push(indent + objectTag(node) + " " + node + (node === rootObj ? " (root)" : ""));
      seen.add(node);

      var kids = childMap.get(node) || [];
      for (var i = 0; i < kids.length; i++) {
        var child = kids[i];
        if (path.has(child)) {
          lines.push(indent + "  " + objectTag(child) + " " + child + " [cycle]");
          continue;
        }
        var nextPath = new Set(path);
        nextPath.add(child);
        walk(child, depth + 1, nextPath);
      }
    }

    if (rootObj && liveSet.has(rootObj)) {
      walk(rootObj, 0, new Set([rootObj]));
    } else if (rootObj) {
      lines.push(objectTag(rootObj) + " " + rootObj + " (root, not live)");
    } else {
      lines.push("(no root assigned)");
    }

    var detached = sortedNames(
      Array.from(liveSet).filter(function (obj) {
        return !seen.has(obj);
      })
    ).sort(objectCompare);

    if (detached.length > 0) {
      lines.push("");
      lines.push("Detached live objects:");
      for (var iDet = 0; iDet < detached.length; iDet++) {
        lines.push("  " + objectTag(detached[iDet]) + " " + detached[iDet]);
      }
    }

    return lines.join("\n");
  }

  function parentOf(stateName, objName) {
    var map = parentByState.get(stateName) || new Map();
    return map.has(objName) ? map.get(objName) : null;
  }

  function summarizeList(items) {
    if (items.length === 0) {
      return "none";
    }
    var preview = items.slice(0, 4).join(", ");
    if (items.length > 4) {
      preview += ", ...";
    }
    return preview;
  }

  function transitionSummary(prevState, currState) {
    if (!prevState) {
      return "initial state";
    }

    var prevLive = liveByState.get(prevState) || new Set();
    var currLive = liveByState.get(currState) || new Set();
    var prevArr = Array.from(prevLive);
    var currArr = Array.from(currLive);

    var added = currArr.filter(function (x) {
      return !prevLive.has(x);
    }).sort(objectCompare);
    var removed = prevArr.filter(function (x) {
      return !currLive.has(x);
    }).sort(objectCompare);
    var stayed = currArr.filter(function (x) {
      return prevLive.has(x);
    });
    var moved = stayed.filter(function (x) {
      return parentOf(prevState, x) !== parentOf(currState, x);
    }).sort(objectCompare);

    var parts = [];
    parts.push("+" + added.length + " [" + summarizeList(added) + "]");
    parts.push("-" + removed.length + " [" + summarizeList(removed) + "]");
    parts.push("moved " + moved.length + " [" + summarizeList(moved) + "]");
    return parts.join(" | ");
  }

  var style = document.createElement("style");
  style.textContent =
    ".fs-wrap{display:flex;flex-wrap:wrap;gap:12px;align-items:flex-start;}" +
    ".fs-card{border:1px solid #c9d1d9;border-radius:8px;padding:10px;background:#ffffff;min-width:320px;max-width:420px;}" +
    ".fs-title{font-weight:700;margin-bottom:6px;}" +
    ".fs-sub{color:#444;margin-bottom:8px;font-size:12px;white-space:pre-line;}" +
    ".fs-pre{margin:0;white-space:pre;line-height:1.35;font-family:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;font-size:12px;}";
  div.appendChild(style);

  var heading = document.createElement("div");
  heading.style.marginBottom = "10px";
  heading.innerHTML =
    "<strong>File-System Trace View</strong><br/>" +
    "<span style='font-size:12px;color:#444'>Legend: [D]=directory, [F]=file, [O]=other object type</span>";
  div.appendChild(heading);

  var wrap = document.createElement("div");
  wrap.className = "fs-wrap";
  div.appendChild(wrap);

  var orderedStates = stateOrder();
  for (var iState = 0; iState < orderedStates.length; iState++) {
    var s = orderedStates[iState];
    var prev = iState > 0 ? orderedStates[iState - 1] : null;

    var card = document.createElement("div");
    card.className = "fs-card";

    var title = document.createElement("div");
    title.className = "fs-title";
    title.textContent = "State " + s;
    card.appendChild(title);

    var sub = document.createElement("div");
    sub.className = "fs-sub";
    sub.textContent = "FsObjs involved: " + transitionSummary(prev, s);
    card.appendChild(sub);

    var pre = document.createElement("pre");
    pre.className = "fs-pre";
    pre.textContent = renderTree(s);
    card.appendChild(pre);

    wrap.appendChild(card);
  }

  if (orderedStates.length === 0) {
    div.textContent = "No states found in this instance.";
  }
})();
