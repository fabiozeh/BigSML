(* BigDecimal library for SML. *)
structure Big = 
struct

	(* Types *) 
	
	datatype prec = Unlimited | Max of int
	type b = (prec * bool * int * int list)
	
	(* Access functions *)

	fun precision (x:b):prec = (#1 x)
	fun positive (x:b):bool = (#2 x)
	fun exponent (x:b):int = (#3 x)
	fun mantissa (x:b):int list = (#4 x)

	(* Internal helper declarations *)

	fun putz 0 m = m | putz n m = putz (n-1) (0::m)
	
	fun morez n (pr,p,e,m) =
		(pr, p, e, rev (putz n (rev m)))

	fun eatz (0::h::m) = eatz (h::m) | eatz (m) = m

	fun maxint a b = if a < b then b else a
	fun minint a b = if a < b then a else b

	val minPrecision = 110
	
	fun maxPrecision _ (Unlimited, _, _, _) = Unlimited
	|	maxPrecision (Unlimited, _, _, _) _ = Unlimited
	|	maxPrecision (Max x, _, _, _) (Max y, _, _, _) = Max (maxint x y)

	fun defaultPrFor x =
		case precision x of
		 Max p => p
		|Unlimited => maxint (length (mantissa x)) minPrecision

	fun inc_exp n (pr,p,e,m):b =
		(pr,p,e+n,putz n m)

	fun isZero (_,_,e,m) = e = 0 andalso m = [0]
	

	(* Useful utility functions *)

	fun truncate (pr,p,e,m) n = 
		(pr,p,e,rev (eatz (rev (List.take(m,minint (length m) n)))))
	
	fun round (pr,p,e,m) n = 
		if length m <= n then (pr,p,e,m) else
		let
			fun aux n [] out = (n, out)
			|	aux 0 (h::l) out = (h, out)
			|	aux n (h::l) out = aux (n-1) l (h::out)
			val (h, m) = aux n m []
			fun sum1 [] carry out = (carry, out)
			|	sum1 (h::l) carry out = 
					sum1 l ((carry+h) div 10) (((carry+h) mod 10)::out)
			val (c, m) = if h >= 5 then sum1 m 1 [] else (0, rev m)
		in
			trim (pr, p, if c > 0 then e + 1 else e, if c > 0 then c::m else m)
		end
	
	and trim ((pr,p,e,0::h::m):b):b = trim (pr,p,e-1,h::m)
	  | trim (Max pr,p,e,m) = round (Max pr,p,e,rev (eatz (rev m))) pr
	  | trim (Unlimited,p,e,m) = (Unlimited,p,e,rev (eatz (rev m)))
	
	fun setPr n (_,p,e,m) = trim (n, p, e, m)
	
	fun fromIntWithPr 0 p = (p, true, 0, [0])
  	|	fromIntWithPr (x:int) (p:prec):b =
	let
		fun fi 0 out n = (n, out)
		|   fi x out n = fi (x div 10) ((x mod 10)::out) (n+1)
		val (e, m) = fi (if x > 0 then x else ~ x) [] ~1
	in
		trim (p, x > 0, e, m)
	end

	fun fromInt n = fromIntWithPr n Unlimited

	fun intLim n l = fromIntWithPr n (Max l)
	
	fun toStringLim n (x:b) =
		let 
			val (pr,p,e,m) = x
			val p = if p then "+" else "-"
			val e = "e" ^ (Int.toString e)
			fun s [] = "0"
				| s (m::mt) = (Int.toString m) ^ s(mt)
		in
			 p ^ (Int.toString (hd m)) ^ "." ^ 
			 s(tl (List.take (m, minint n (length m)))) ^ e
		end

	fun toString (x:b) = toStringLim 10 x

	fun toFullString x = toStringLim (length (mantissa x)) x


	(* Operations *)

	fun minus (pr,p,e,m):b = (pr, not p, e, m)
	
	fun compareabs (x, y) =
		let
			val p = maxPrecision x y
			val x = setPr p x
			val y = setPr p y
			(*val _ = print ("comp: (" ^ 
				(toString x) ^ ", " ^ (toString y) ^ ")\n") *)
			fun compm [] [] = EQUAL
				| compm [] b = LESS
				| compm a [] = GREATER
				| compm (a::at) (b::bt) =
				if a > b then GREATER
				else if a < b then LESS
				else compm at bt 
		in
			if isZero y then GREATER
			else if exponent x > exponent y then GREATER
			else if exponent x < exponent y then LESS
			else compm (mantissa x) (mantissa y)
		end
		
	fun sub_ (x, y):b =
		case compareabs(x,y) of
			EQUAL => (precision x, true, 0, [0])
		|   LESS => minus (sub_(y, x))
		|   GREATER =>
		let
			val (xe, ye) = (exponent x, exponent y)
			val x = if xe >= ye then x else inc_exp (ye - xe) x
			val y = if xe > ye then inc_exp (xe - ye) y else y
			val diffm = length (mantissa x) - length (mantissa y)
			val x = if diffm >= 0 then x else morez (~diffm) x
			val y = if diffm > 0 then morez diffm y else y
			fun subdig [] [] carry out = out
			|   subdig [] (b::bt) carry out = out (* impossible *)
			|   subdig (a::at) [] carry out = out (* impossible *)
			|   subdig (a::at) (b::bt) carry out =
				let 
					val dig = if (a - carry) >= b then a-b-carry else a + 10 - b - carry
					val carry = if (a - carry) >= b then 0 else 1
				in
					subdig at bt carry (dig::out)
				end
		in
			trim (
				maxPrecision x y,
				(true),
				(exponent x),
				(subdig (rev (mantissa x)) (rev (mantissa y)) 0 [])
			)
		end

	fun add (x, y):b =
		let
			val (xe, ye) = (exponent x, exponent y)
			val x = if xe >= ye then x else inc_exp (ye - xe) x
			val y = if xe > ye then inc_exp (xe - ye) y else y
			val diffm = length (mantissa x) - length (mantissa y)
			val x = if diffm >= 0 then x else morez (~diffm) x
			val y = if diffm > 0 then morez diffm y else y
			fun sumdig [] [] carry out = carry::out
			|   sumdig [] (b::bt) carry out = 
					sumdig [] bt ((b+carry) div 10) (((b+carry) mod 10)::out)
			|   sumdig (a::at) [] carry out =
					sumdig at [] ((a+carry) div 10) (((a+carry) mod 10)::out)
			| sumdig (a::at) (b::bt) carry out =
				sumdig at bt ((a+b+carry) div 10) (((a+b+carry) mod 10)::out)
		in
			if positive x andalso positive y then 
				trim (
					maxPrecision x y,
					(positive x),
					(exponent x) + 1,
					(sumdig (rev (mantissa x)) (rev (mantissa y)) 0 [])
				)
			else if positive x then
				sub_ (x, minus y)
			else if positive y then 
				sub_ (y, minus x)
			else 
				trim (
					maxPrecision x y,
					(positive x),
					(exponent x) + 1,
					(sumdig (rev (mantissa x)) (rev (mantissa y)) 0 [])
				)
		end
	
	fun sub (x, y):b =
		if positive x andalso positive y then sub_ (x, y)
		else if positive x then add (x, minus y)
		else if positive y then add (y, minus x)
		else sub_ (x, y)

	fun multl (x, y):b =
		let
			fun term dig [] carry out = carry::out
			| term dig (x::xt) carry out = 
				term dig xt ((dig*x + carry) div 10) (((dig*x + carry) mod 10)::out)
			val sign = ((positive x) andalso (positive y)) orelse
			((not (positive x)) andalso (not (positive y)))
			val first = (maxPrecision x y, sign, 0, [0])
			val ex1 = (exponent y) + (exponent x) - (length (mantissa x)) + 2
			val (_, acc) = List.foldr 
			  (fn (x,(ex,(pr,p,e,m))) => (ex+1, add (
			  	(pr,p,ex,term x (rev (mantissa y)) 0 []),
			  	(pr,p,e,m))))
			  (ex1,first)
			  (mantissa x)
			 in acc
		end

	fun newton_raphson (k:b) (f:b->b) (ep:b):b =
		let
			val kp1 = f k
			val error = sub (kp1, k)
			(* val _ = print (
				"error n_r(" ^ (toString k) ^ 
				", ep=" ^ (toString ep) ^ ") = " ^
				(toString error) ^ "\n") *)
		in
			if compareabs (ep, sub (kp1, k)) = LESS
			then newton_raphson kp1 f ep
			else kp1
		end

	fun reciprocal (x:b):b =
		let
			val pr = defaultPrFor x
			val ep = (Max pr, true, ~ (pr-1), [5])
			val two = (Max pr, true, 0, [2])
			val pointone = (Max pr, true, ~(1+(exponent x)), [1])
			fun iter k = multl (k, sub (two, multl (x, k)))
		in
			newton_raphson pointone iter ep
		end

	fun divide (x, y):b = multl (x, reciprocal y)

	fun sqrt (x:b):b =
		let
			val pr = defaultPrFor x
			val ep = (Max pr, true, ~ (pr-1), [5])
			val half = (Max pr, true, ~1, [5])
			fun iter k = multl(half, add(k, divide(x, k)))
			(* val _ = print ("==  sqrt of " ^ (toString x) ^ " ==\n") *)
		in
			newton_raphson x iter ep
		end
end;
