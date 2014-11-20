cis
===

Compact Integer Sets

This library implements compact integer sets, represented as a list of
integer intervals. The usual set operations are provided.  The
advantage compared to ordered lists is that the actual size may be
smaller than the cardinal of a set when many elements are
contiguous. Most set operations are linear w.r.t. the size of the
structure, not the cardinality of the set.

Author: Sébastien Ferré <ferre -at- irisa.fr>

Ported to Standard ML by Ivan Raikov.


CIS         -Signature-

    type t (** Type of cis *)

    val max_elt : t -> int

[max_elt cis] returns the maximum integer in [cis]. Takes constant time.

    val min_elt : t -> int

[min_elt cis] returns the minimum integer in [cis]. Takes linear time.

    val empty : t

[empty] is the empty set.

    val is_empty : t -> bool

[is_empty cis] returns whether [cis] is the empty set. 

    val cardinal : t -> int

[cardinal cis] returns the cardinal of [cis]. Takes linear time in the size of [cis]. 

    val member : int * t -> bool

[mem x cis] returns whether [x] belongs to [cis]. Takes linear time in the size of [cis].

    val singleton : int -> t

[singleton x] returns a singleton set with element [x]. 

    val interval : int * int -> t

[interval x y] returns a singleton set with the range [x..y]. 

    val add : int * t -> t

[add x cis] adds element [x] to [cis]. 

Takes linear time in the size of [cis], but constant time when [x] is greater than any element in [cis].
Not tail-recursive. 

    val remove : int * t -> t

[remove x cis] removes element [x] from [cis]. Not tail-recursive. 

    val fromList : int list -> t

[fromList l] builds a cis from an integer list. 

    val union : t * t -> t

The set union. 

    val intersection : t * t -> t

The set intersection. 

    val difference : t * t -> t

The set difference. 

    val app : (int -> unit) -> t -> unit

Iteration on the elements of a cis. 

    val foldl : (int * 'a -> 'a) -> 'a -> t -> 'a

Left folding. Elements are visited in decreasing order. 

    val foldr : (int * 'a -> 'a) -> 'a -> t -> 'a

Right folding. Integers are visited in increasing order. 

    val elements : t -> int list

[elements cis] returns the elements of [cis] as list of decreasing integers. 
