
structure CisTest =
struct

open Cis

val minKey = 1
val maxKey = 10000

fun decr (x) = x-1
fun incr (x) = x+1


exception AssertionFailed

fun assert true = ()
  | assert false = raise AssertionFailed


val a =	 (* loading a sequence [minKey ... maxKey] in ascending order *)
    let
        fun recur (i, l) =
	    let val t' = add (i, l)
            in
		assert (member (i, t'));
                if i < maxKey
                then recur (incr i, t')
                else l
            end
    in
        recur (minKey, empty)
    end

val _ = print ("max_elt(a) = " ^ (Int.toString (Cis.max_elt(a))) ^ "\n")
val _ = print ("min_elt(a) = " ^ (Int.toString (Cis.min_elt(a))) ^ "\n")
val _ = print ("cardinal(a) = " ^ (Int.toString (Cis.cardinal(a))) ^ "\n")

val b = (* adding elements out of order *)
    let
        val t = add (4, add (1, add (5, empty)))
    in
        assert (elements (t) = [5,4,1]);
        t
    end

val l1 = interval (minKey, maxKey div 2)
val l2  = interval (maxKey div 2, maxKey)

val _ = 
    (
      assert (member (minKey, l1));
      assert (member (maxKey div 2, l1));
      assert (not (member (maxKey, l1)));
      assert (not (member ((maxKey div 2)+1, l1)));
      assert (not (member (minKey, l2)));
      assert (member (maxKey div 2, l2));
      assert (member (maxKey, l2));
      assert (member ((maxKey div 2)+1, l2));
      assert (member (minKey, union (l1, l2)));
      assert (member (maxKey div 2, union (l1, l2)));
      assert (member (maxKey, union (l1, l2)));
      assert (member ((maxKey div 2)+1, union (l1, l2)));
      assert (not (member (minKey, intersection (l1, l2))));
      assert (member (maxKey div 2, intersection (l1, l2)));
      assert (not (member (maxKey, intersection (l1, l2))));
      assert (not (member (1 + (maxKey div 2), intersection (l1, l2))));
      assert (not (member (minKey, difference (union (l1, l2), l1))));
      assert (not (member (maxKey div 2, difference (union (l1, l2), l1))));
      assert (member (maxKey, difference (union (l1, l2), l1)));
      assert (member (1 + (maxKey div 2), difference (union (l1, l2), l1)))
    )

end

