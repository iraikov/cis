(**
   Cis : compact integer sets

   This module implements compact integer sets, represented as a
   (custom) list of integer intervals. Usual set operations are
   provided.  The advantage compared to ordered lists is that the
   actual size may be smaller than the cardinal of a set when many
   elements are contiguous. Most set operations are linear w.r.t. the
   size of the structure, not the cardinality of the set.

   Author: Sébastien Ferré <ferre@irisa.fr>
   License: LGPL
   Ported to Standard ML by Ivan Raikov
*)

signature CIS =
sig

    type t (** Type of cis *)

    val max_elt : t -> int
    (** [max_elt cis] returns the maximum integer in [cis]. Takes constant time. *)
    val min_elt : t -> int
    (** [min_elt cis] returns the minimum integer in [cis]. Takes linear time. *)
    val empty : t
    (** [empty] is the empty set. *)
    val is_empty : t -> bool
    (** [is_empty cis] returns whether [cis] is the empty set. *)
    val cardinal : t -> int
    (** [cardinal cis] returns the cardinal of [cis]. Takes linear time in the size of [cis]. *)
    val member : int * t -> bool
    (** [mem x cis] returns whether [x] belongs to [cis]. Takes linear time in the size of [cis]. *) 
    val singleton : int -> t
    (** [singleton x] returns a singleton set with element [x]. *)
    val interval : int * int -> t
    (** [interval x y] returns a singleton set with the range [x..y]. *)
    val add : int * t -> t
    (** [add x cis] adds element [x] to [cis]. 
        Takes linear time in the size of [cis], but constant time when [x] is greater than any element in [cis].
        Not tail-recursive. *)
    val remove : int * t -> t
    (** [remove x cis] removes element [x] from [cis]. Not tail-recursive. *)
    val fromList : int list -> t
    (** [of_list l] builds a cis from an integer list. *)
    val union : t * t -> t
    (** The set union. *)
    val intersection : t * t -> t
    (** The set intersection. *)
    val difference : t * t -> t
    (** The set difference. *)
    val app : (int -> unit) -> t -> unit
    (** Iteration on the elements of a cis. *)
    val foldl : (int * 'a -> 'a) -> 'a -> t -> 'a
    (** Left folding. Elements are visited in decreasing order. *)
    val foldr : (int * 'a -> 'a) -> 'a -> t -> 'a
    (** Right folding. Integers are visited in increasing order. *)
    val elements : t -> int list
    (** [elements cis] returns the elements of [cis] as list of decreasing integers. *)

end

structure Cis: CIS =
struct

(* copied from module Common *)

(* end of copy *)

type elt = int

datatype t = Empty
           | Single of int * t
           | Interv of int * int * t
           (** integers in decreasing order *)

exception InvalidArgument of string

fun max_elt (x) : int =
    case x of
        Empty => raise (InvalidArgument "Cis.max_elt: set is empty")
      | Single (x,_) => x
      | Interv (xmax,_,_) => xmax

fun min_elt (x : t) : int =
    case x of
        Empty => raise (InvalidArgument "Cis.max: set is empty")
      | Single (x,Empty) => x
      | Interv (_,xmin,Empty) => xmin
      | Single (_,l) => min_elt l
      | Interv (_,_,l) => min_elt l

val step : t -> {nil_step:(unit -> 'a), single_step:(int * t -> 'a), interv_step:((int * int) * t -> 'a)} -> 'a =
  fn l =>
     fn {nil_step, single_step, interv_step} =>
        case l of
          Empty => nil_step ()
         | Single (x,l') => single_step (x, l')
         | Interv (x,y,l') => interv_step ((x,y), l')


val cons_single : int * t -> t =
  fn (x, l) =>
     step l
          {nil_step = (fn () => Single (x,Empty)),
           single_step = (fn (x', l') => (* assert (x > x');*) 
                             if x=x'+1 then Interv (x,x',l') else Single (x,l)),
           interv_step = (fn ((xmax',xmin'),l') => (* assert (x > xmax');*) 
                             if x=xmax'+1 then Interv (x,xmin',l') else Single (x,l))}


fun cons_interval ((xmax,xmin) : (int * int), l: t) : t =
    if xmax > xmin 
    then
        (step l
	      {nil_step = (fn () => Interv (xmax, xmin, Empty)),
	       single_step= (fn (x', l') => (* assert (xmin > x');*) 
                                if xmin=x'+1 then Interv (xmax,x',l') else Interv (xmax,xmin,l)),
	       interv_step = (fn ((xmax',xmin'), l') => (* assert (xmin > xmax');*) 
                                 if xmin=xmax'+1 then Interv (xmax, xmin', l') 
                                 else Interv (xmax,xmin,l))})
    else
        if xmin=xmax 
        then cons_single (xmin, l)
        else (* xmin > xmax *) cons_interval ((xmin,xmax),l)


val empty : t = Empty


val is_empty : t -> bool =
  fn l => (l = Empty)


val cardinal : t -> int =
    let
        fun recur (accu, l) =
            step l
                 {nil_step = (fn () => accu),
                  single_step = (fn (x, l') => recur (accu+1,l')),
                  interv_step = (fn ((xmax,xmin), l') => recur (accu+xmax-xmin+1,l'))}
    in
        fn l => recur (0, l)
    end


fun member (e : elt, l : t) : bool =
    step l
      {nil_step = (fn () => false),
       single_step = (fn (x, l_tail) =>
	            e=x orelse (x > e andalso member (e, l_tail))),
       interv_step = (fn ((xmax,xmin),l_tail) =>
	                 (xmax >= e andalso e >= xmin) orelse
                         (xmin > e andalso member (e, l_tail)))}


fun singleton (x : elt) : t = Single (x,Empty)


fun interval (xmin, xmax) =
    if xmin > xmax
    then interval (xmax, xmin)
    else (if xmin = xmax
          then singleton xmin
          else (Interv (xmax, xmin, Empty)))


fun add (x : int, l: t) : t =
    step l
         {nil_step = (fn () => cons_single (x, l)),
          single_step = (fn (x', l') =>
	               if x > x' 
                       then cons_single (x, l)
	               else (if x = x' then l
	                     else (* x' > x *) cons_single (x', add (x, l')))),
          interv_step = (fn ((xmax',xmin'), l') =>
	                    if x > xmax' 
                            then cons_single (x, l)
	                    else (if xmax' >= x andalso x >= xmin' 
                                  then l else (* xmin' > x *) cons_interval ((xmax',xmin'), add (x, l'))))}
                       

fun remove (x : int, l: t) : t =
    step l
         {nil_step = (fn () => empty),
          single_step = (fn (x', l') =>
	               if x > x' then l
	               else if x = x' then l'
	               else (* x' > x *) cons_single (x', remove (x, l'))),
          interv_step = (fn ((xmax',xmin'), l') =>
	                    if x > xmax' then l
	                    else (if xmax' >= x andalso x >= xmin' 
                                  then cons_interval ((xmax',x+1),cons_interval ((x-1,xmin'), l'))
	                          else cons_interval ((xmax',xmin'),remove (x, l'))))}


val fromList : int list -> t =
  fn l => List.foldl add empty l


fun union (l1, l2) =
    step l1
	 {nil_step = (fn () => l2),
          single_step = (fn (x', l') =>
                       step l2 
                            {nil_step = (fn () => l1),
		             single_step = (fn (x'', l'') =>
                                          if x' > (x'' + 1)
                                          then cons_single (x', union (l', l2))
                                          else (if x'' > (x' + 1)
                                                then cons_single (x'', union (l1, l''))
                                                else (if x' = (x'' + 1)
                                                      then cons_interval ((x',x''),union(l',l''))
                                                      else (if x'' = (x' + 1)
                                                            then cons_interval ((x'',x'),union(l',l''))
                                                            else cons_single (x', union (l',l'')))))),
                             interv_step = (fn ((xmax'',xmin''), l'') =>
		                               if x' > xmax''
                                               then cons_single (x', union (l', l2))
                                               else (if xmin'' > (x' + 1)
                                                     then cons_interval ((xmax'', xmin''), union (l1, l''))
                                                     else (if xmin'' = (x' + 1)
                                                           then cons_interval ((xmax'', x'), union (l', l''))
			                                   else cons_interval ((xmax'', x'), 
                                                                               union (l', cons_interval ((x'-1,xmin''),l''))))))}),
          interv_step = (fn ((xmax',xmin'), l') =>
                            step l2
                                 {nil_step = (fn () => l1),
		                  single_step = (fn (x'', l'') =>
                                                    if (x'' > xmax')
                                                    then cons_single (x'', union (l1, l''))
                                                    else (if xmin' > (x'' + 1) 
                                                          then cons_interval ((xmax', xmin'), union (l', l2))
                                                          else (if xmin' = (x'' + 1)
                                                                then cons_interval ((xmax', x''), union (l', l''))
			                                        else cons_interval ((xmax', x''), 
                                                                                    union (cons_interval ((x''-1,xmin'),l'), l''))))),
		                  interv_step = (fn ((xmax'',xmin''), l'') =>
                                                    if xmin'' > xmax'
                                                    then cons_interval ((xmax'', xmin''), union (l1, l''))
                                                    else (if xmin' > xmax' 
                                                          then cons_interval ((xmax', xmin'), union (l', l2))
                                                          else cons_interval ((Int.max (xmax', xmax''), Int.max (xmin', xmin'')),
                                                                              if xmin' = xmin''
                                                                              then union (l', l'')
                                                                              else (if xmin' > xmin''
                                                                                    then union (l', cons_interval ((xmin'-1,xmin''-1),l''))
                                                                                    else union (cons_interval ((xmin''-1,xmin'),l'),l'')))))})}
         
         
fun intersection (l1, l2) =
    step l1
         {nil_step = (fn () => empty),
          single_step = (fn (x', l') =>
	                    step l2
	                         {nil_step = (fn () => empty),
	                          single_step = (fn (x'', l'') =>
	                                            if x' > 1+x'' 
                                                    then intersection (l', l2)
	                                            else (if x'' > 1+x' 
                                                          then intersection (l1, l'')
	                                                  else (if x' = 1+x''
                                                                then intersection (l', l'')
	                                                        else (if x'' = 1+x' then intersection (l', l'')
	                                                              else (* x1=x2 *) cons_single (x', intersection (l', l'')))))),
	                          interv_step = (fn ((xmax'',xmin''),l'') =>
	                                            if x' > xmax''
                                                    then intersection (l', l2)
	                                            else (if xmin'' > x'
                                                          then intersection (l1, l'')
	                                                  else (* xmax2 >= x1 & x1 >= xmin2 *) cons_single (x', intersection (l', l2))))}),
          interv_step = (fn ((xmax',xmin'),l') =>
	                    step l2
	                         {nil_step = (fn () => empty),
	                          single_step = (fn (x'', l'') =>
	                                            if x'' > xmax'
                                                    then intersection (l1, l'')
	                                            else (if xmin' > x''
                                                          then intersection (l', l2)
	                                                  else (* xmax1 >= x2 & x2 >= xmin1 *) cons_single (x'', intersection (l1, l'')))),
	                          interv_step = (fn ((xmax'',xmin''), l'') =>
	                                            if xmin'' > xmax'
                                                    then intersection (l1, l'')
	                                            else (if xmin' > xmax''
                                                          then intersection (l', l2)
	                                                  else cons_interval
		                                                   ((Int.min (xmax', xmax''), Int.max (xmin', xmin'')),
		                                                    (if xmin' >= xmin'' 
                                                                     then intersection (l', l2)
                                                                     else intersection (l1, l'')))))})}

fun difference (l1, l2) =
    step l1
         {nil_step = (fn () => empty),
          single_step = (fn (x', l') =>
	                    step l2
	                         {nil_step = (fn () => l1),
	                          single_step = (fn (x'', l'') =>
	                                            if x' > x'' 
                                                    then cons_single (x', difference (l', l2))
	                                            else (if x'' > x' 
                                                          then difference (l1, l'')
	                                                  else (* x1=x2 *) difference (l', l''))),
	                          interv_step = (fn ((xmax'',xmin''),l'') =>
	                                            if x' > xmax'' 
                                                    then cons_single (x', difference (l', l2))
	                                            else (if xmin'' > x' 
                                                          then difference (l1, l'')
	                                                  else (* xmax2 >= x1 & x1 >= xmin2 *) difference (l', l2)))}),
          interv_step = (fn ((xmax',xmin'),l') =>
	                    step l2
	                         {nil_step = (fn () => l1),
	                          single_step = (fn (x'', l'') =>
	                                            if x'' > xmax'
                                                    then difference (l1, l'')
	                                            else (if xmin' > x''
                                                          then cons_interval ((xmax',xmin'), difference (l', l2))
	                                                  else (* xmax1 >= x2 & x2 >= xmin1 *) 
                                                              cons_interval ((xmax',x''+1),
                                                                             difference (cons_interval ((x''-1,xmin'), l'), l'')))),
	                          interv_step = (fn ((xmax'',xmin''), l'') =>
	                                            if xmin'' > xmax'
                                                    then difference (l1, l'')
	                                            else (if xmin' > xmax''
                                                          then cons_interval ((xmax',xmin'), difference (l', l2))
	                                                  else cons_interval
                                                                   ((xmax',xmax''+1),
		                                                    (if xmin' >= xmin''
		                                                     then difference (l', l2)
		                                                     else difference (cons_interval ((xmin''-1,xmin'),l'), l'')))))})}

structure Loop =
    struct
        fun all (a, b, f) =
            if a > b then
                true
            else if f a then
                all (a+1, b, f)
            else
                false

        fun any (a, b, f) =
            if a > b then
                false
            else if f a then
                true
            else
                any (a+1, b, f)

        fun app (a, b, f) =
            if a < b then
                (f a; app (a+1, b, f))
            else
                ()

        fun app2 (a1, b1, a2, b2, f) =
            if ((a1 < b1) andalso (a2 < b2)) then
                (f (a1, a2); app2 (a1+1, b1, a2+1, b2, f))
            else ()

        fun app' (a, b, d, f) =
            if a < b then
                (f a; app' (a+d, b, d, f))
            else
                ()

        fun app_downto (a, b, f) =
            if a > b then
                (f a; app_downto (a-1, b, f))
            else
                ()

        fun foldi (a, b, f, init) =
            if a < b then
                foldi (a+1, b, f, f (a, init))
            else
                init

        fun foldi_downto (a, b, f, init) =
            if a > b then
                foldi_downto (a-1, b, f, f (a, init))
            else
                init
    end


fun app (proc: elt -> unit) (l: t) : unit =
    step l
         {nil_step = (fn () => ()),
          single_step = (fn (x, l_tail) => (proc x; app proc l_tail)),
          interv_step = (fn ((xmax,xmin), l_tail) =>
	                    (Loop.app_downto (xmax, xmin, proc);
	                     app proc l_tail))}


fun foldl (f : (elt * 'a -> 'a)) (e : 'a) (l : t) : 'a =
    step l
         {nil_step = (fn () => e),
          single_step = (fn (x, l_tail) => foldl f (f (x,e)) l_tail),
          interv_step = (fn ((xmax,xmin),l_tail) =>
	                    foldl f (Loop.foldi_downto (xmax, xmin-1, fn (x, res) => f (x, res), e)) l_tail)}


fun foldr (f : (elt * 'a -> 'a)) (e : 'a) (l : t) : 'a =
    step l
         {nil_step = (fn () => e),
          single_step = (fn (x, l_tail) =>
	                    f (x, foldr f e l_tail)),
          interv_step = (fn ((xmax,xmin),l_tail) =>
	                    Loop.foldi (xmin, xmax+1, fn (x, res) => f (x, res), foldr f e l_tail))}

fun elements (l : t) : elt list =
    List.rev (foldl (op ::) [] l)


end

