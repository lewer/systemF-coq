var trans_time = 500;

/** Proofs are code blocks beginning with "Proof" */
var proofs = $("span:contains('Proof')").parent('.code');

/** Hides a proof and show a button */
function hideProof(p, t) {
    var link = $('<input type="button" class="proof_but" value="Afficher la preuve"/>');
    link.click(function() {
        showProof(p, trans_time);
        $(this).remove();
    })
    p.before(link);
    p.slideUp(t);
}

/** Shows a proof and show a button */
function showProof(p, t) {
    var link = $('<input type="button" class="proof_but" value="Masquer la preuve"/>');
    link.click(function() {
        hideProof(p, trans_time);
        $(this).remove();
    })
    p.before(link);
    p.slideDown(t);
}

/** Hide all proofs */
function hideThemAll(p){
    p.each(function() {
        hideProof($(this), 0);
    });
}


/** Draw a top navigation bar */
function active(name) {
    var url = window.location.pathname;
    var filename = url.substring(url.lastIndexOf('/')+1);

    if(name == filename) return " active"; else return "";
}

function drawNav() {
    var nav = $('<div id="navbar">' +
        '<span class="nav_item '+active('F00_docindex.html')+'"><a href="F00_docindex.html" alt="Introduction et sommaire">ACCUEIL</a></span>' +
        '<span class="nav_item '+active('F01_Defs.html')+'"><a href="F01_Defs.html" alt="Defs">I</a></span>' +
        '<span class="nav_item '+active('F02_Inference.html')+'"><a href="F02_Inference.html" alt="Inference">II</a></span>' +
        '<span class="nav_item '+active('F03_Insert_kind.html')+'"><a href="F03_Insert_kind.html" alt="Insert_kind">III</a></span>' +
        '<span class="nav_item '+active('F04_Remove_var.html')+'"><a href="F04_Remove_var.html" alt="Remove_var">IV</a></span>' +
        '<span class="nav_item '+active('F05_Env_subst.html')+'"><a href="F05_Env_subst.html" alt="Env_subst">V</a></span>' +
        '<span class="nav_item '+active('F06_Regularity.html')+'"><a href="F06_Regularity.html" alt="Regularity">VI</a></span>' +
        '<span class="nav_item '+active('F07_Normalisation.html')+'"><a href="F07_Normalisation.html" alt="Normalisation">VII</a></span>' +
        '</div>')
    $("body").prepend(nav);
}


/** At loading time : */
hideThemAll(proofs);
drawNav();
