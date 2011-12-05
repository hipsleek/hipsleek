/**
 Display module to populate content of the HTML
 @author Vu An Hoa
 */

function getHTML(obj) {
	if (obj.type == "precnd" && obj.is_primitive == "true")
		return "";

	var result = "<div class=\"" + obj.type + "\"";
	if (obj.type == "proc") {
		result += " id=\"content-proc-" + obj.name + "\">";
		result += "<table class=\"verification-table\">"
		for(var i = 0; i < obj.items.length; i++) {
			var itemhtml = getHTML(obj.items[i]);
			if (itemhtml != "")
				result += "<tr><td class=\"expandable\">" + itemhtml + "</td></tr>";
		}
		result += "</table>"
	} else if (obj.type == "precnd_arracc") {
		result += ">" + "<b>Array access at line " + obj.line + "</b>";
	} else if (obj.type == "precnd_arrupdt") {
		result += ">" + "<b>Array update at line " + obj.line + "</b>";
	} else if (obj.type == "precnd") {
			result += ">" + "<b>Procedure call at line " + obj.line + "</b>";
	}	else if (obj.type == "post") {
		result += ">" + "<b>Post-condition" + "</b>";
	} else if (obj.type == "assert") {
		result += ">" + "<b>Assertion at line " + obj.line + "</b>";
	} else if (obj.type == "pureimply") {
		if (obj.is_valid == "true")
				cls = "ok";
			else
				cls = "notok";
		result += ">" + "<span class=\"" + cls + "\">" + obj.formula + "</span>";
	} else result += ">";

	if (obj.type != "proc") {
		result += "<div class=\"childs\">";
		if (obj.items != null) {
			for(var i = 0; i < obj.items.length; i++) {
				result += getHTML(obj.items[i]);
			}
		}
		result += "</div>";
	}
	result += "</div>";
	return result;
}

var currently_displayed_id = "";

function idFromNavId(navid) {
	// simply take out the prefix "nav" to get the id
	return navid.substring(3);
}

function navId(id) {
	return "nav" + id;
}

function contentId(id) {
	return "content" + id;
}

// Set up the HTML DOM
function setup() {
	// Load the json file
	
	// Set the file name in the header
	$("#header").html(srcfilename);
	// Generate HTML content and set up the navigation panel with appropriate call back functions
	var content_proc = "";
	for(i = 0; i < jsonproof.length; i++) {
		var p = jsonproof[i];
		if (p.type == "proc") {
			content_proc += getHTML(p);
			var navid = "nav-proc-" + p.name;
			var cls;
			if (p.success == "true")
				cls = "ok";
			else
				cls = "notok";
			$("#nav-proc-list").append("<li><span id=\"" + navid + "\" class=\"" + cls + "\">" + p.name + "</span></li>");
			$("#" + navid).click(function(){
				var orgid = this.id.substring(3);
				if (currently_displayed_id != "") {
					$("#content"+currently_displayed_id).hide();
					$("#nav"+currently_displayed_id).removeClass("selected");
				}
				$("#"+this.id).addClass("selected");
				$("#content"+orgid).show();
				currently_displayed_id = orgid;
			});
		}
	}
	$("#content").html(content_proc);
	for(i = 0; i < jsonproof.length; i++) {
		var p = jsonproof[i];
		if (p.type == "proc") {
			$("#content-proc-" + p.name).hide();
		}
	}
	$(".expandable").click(function() {
		$("div.childs",this).slideToggle("fast");
	});
}
