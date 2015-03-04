var trans_time = 500;

/** Proofs are code blocks beginning with "Proof" */
var proofs = $("span:contains('Proof')").parent('.code');

/** Hides a proof and show a button */
function hideProof(p, t) {
    var link = $('<input type="button" value="Afficher la preuve"/>');
    link.click(function() {
        showProof(p, trans_time);
        $(this).remove();
    })
    p.before(link);
    p.slideUp(t);
}

/** Shows a proof and show a button */
function showProof(p, t) {
    var link = $('<input type="button" value="Masquer la preuve"/>');
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

hideThemAll(proofs);