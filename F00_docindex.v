(** #<span class="titre">#Une formalisation de System F en Coq#</span># *)
(** * Introduction *)
(** L'objectif de ce projet est de formaliser en Coq une version du Système F (à savoir, avec une hierarchie de sorte), avec pour but de prouver la normaisation forte de ce système. Nous suivons la preuve décrite dans l'article de Harley D. Eades III et Aaron Stump [[1]].
Nous n'avons pas atteint cet objectif qui est relativement ambitieux mais nous avons tout de même réussi à montrer quelques propriétés non triviales de ce système : cumulativité, régularité et inférence notamment.
Ce rapport prend la forme d'une documentation générée par [coqdoc] dont les nombreux commentaires devraient permettre de suivre facilement notre démarche. *)

(** * Sommaire *)
(** - #<a href="F01_Defs.html">#Définitons et premières propriétés#</a># *)
(** - #<a href="F02_Inference.html">#Inférences de kinds et de types#</a># *)
(** - #<a href="F03_Insert_kind.html">#Insert kind#</a># *)
(** - #<a href="F04_Env_subst.html">#Subtitutions dans l'environnement#</a># *)