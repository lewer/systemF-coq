(** #<span class="titre">#Une formalisation de System F en Coq#</span># *)
(** * Introduction *)
(** L'objectif de ce projet est de formaliser en Coq une version stratifiée du Système F (à savoir, avec une hierarchie de sortes), avec pour objectif de prouver la forte normalisation de ce système. Nous suivons la preuve décrite dans l'article de Harley D. Eades III et Aaron Stump.
Nous n'avons pas atteint cet objectif qui est relativement ambitieux mais nous avons tout de même réussi à montrer quelques propriétés non triviales de ce système : cumulativité, régularité et inférence notamment.
Ce rapport prend la forme d'une documentation générée par [coqdoc] dont les nombreux commentaires devraient permettre au lecteur de suivre facilement notre démarche. *)

(** * Sommaire *)
(** - #<a href="F01_Defs.html">#I - Définitons et premières propriétés#</a># *)
(** - #<a href="F02_Inference.html">#II - Inférences de sorte et de type#</a># *)
(** - #<a href="F03_Insert_kind.html">#III - Affaiblissement par déclaration d'une sorte#</a># *)
(** - #<a href="F04_Remove_var.html">#IV - Affaiblissement par déclaration d'un type#</a># *)
(** - #<a href="F05_Env_subst.html">#V - Subtitution dans l'environnement#</a># *)
(** - #<a href="F06_Regularity.html">#VI - Régularité#</a># *)
(** - #<a href="F07_Normalisation.html">#VII - Normalisation et conclusion#</a># *)