function badState(o) {
  return o[1].hasOwnProperty("Left")
}

function stringy(o) {
  if (o.hasOwnProperty("VInR"))
    return "InR(" + stringy(o.VInR) + ")";
  if (o.hasOwnProperty("VInL"))
    return "InL(" + stringy(o.VInL) + ")";
  if (o.hasOwnProperty("VUnInit"))
    return "-"
  return JSON.stringify(o);
}

function printState(fields, s)
{
  var row = '<tr>';
  for (v in fields) {
    row += '<td>' + stringy(s[fields[v]]) + '</td>';
  }
  row += '</tr>\n';
  $("#theTable").append(row);
}

function printBadTrace(trace) {
  var fields = [];
  $("#selectedFields li").each(function (e) {
    fields.push($(this).attr("value"));
  });
  var header = '<tr>';
  for (v in fields) {
    header += '<th>' + fields[v] + '</th>';
  }
  header += "</tr>";
  $("#theTable").append(header);
  s0 = trace[0];
  srest = trace[1].Left;
  for (i in srest) {
    printState(fields, srest[i][0]);
  }
  printState(fields, s0);
}

function populateFields(s) {
  options = "";
  for (f in s) {
    options += "<li value=\""+f+"\"><i class='fa fa-bars'></i>"+ f + "</li>";
  }
  $("#disabledFields").append(options);
}

var badStates = [];
function printTraces() {
  $("#theTable").empty();
  if (badStates.length > 0) {
    printBadTrace(badStates[0]);
  } else {
    alert("No Bad Traces!");
  } 
}

function go(states) {
  badStates = states.filter(badState);
  if (badStates.length > 0) {
    populateFields(states[0][0]);
    Sortable.create(selectedFields, { group : 'shared', onSort: function (evt) { printTraces() } });
    Sortable.create(disabledFields, { group : 'shared'});
  } else {
    alert ("No Bad Traces!");
  }
};

window.onload = function (event) {
  go(states);
}
