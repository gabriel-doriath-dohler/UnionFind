let max_rang = ref 0;;
type partition = (int * int) array;;

let init n =
	Array.init n (fun i -> (i, 0));;


let rec find t i =
	(* Non récursif terminal. On peut faire un  version itérative. *)
	if fst t.(i) = i then
		i
	else begin
		let racine = find t (fst t.(i)) in
		t.(i) <- (racine, snd t.(i)); (* Compression de chemin. *)
		racine
	end;;


let union t x y =
	let i = find t x in
	let j = find t y in
	let rec aux t i j =
		(* Union par rang. *)
		if snd t.(i) <= snd t.(j) then begin
			t.(i) <- (j, snd t.(i));
			if snd t.(i) = snd t.(j) then begin
				t.(j) <- (fst t.(j), snd t.(j) + 1);
				max_rang := max !max_rang (snd t.(j))
			end
		end
		else begin
			aux t j i
		end
	in if i <> j then aux t i j;;


(* Calcul de composantes connexes. *)
type voisin = int list;;
type graphe = voisin array;;


let composantes g =
	let r = init (Array.length g) in
	for i = 0 to Array.length g - 1 do
		List.iter (fun x -> union r i x) g.(i)
	done;
	r;;


let nb_classes a =
	(* On pourrait aussi stocker le nombre de classes d'équivalence dans la structure union find. *)
	let c = ref 0 in
	for i = 0 to Array.length a - 1 do
		if fst a.(i) = i then
			incr c
	done;
	!c;;


let nb_composantes g =
	let r = composantes g in
	nb_classes r;;


(* Test de la performance de union find. *)
(*
La complexité est en O(hauteur).
On calcule donc la hauteur maximale des arbres pour k structures union find de taille n.
*)
let rd_union t n =
	union t (Random.int n) (Random.int n);;


let rd_union_find n =
	let t = init n in
	for i = 1 to 100000 do
		rd_union t n
	done;
	t;;


let n = 100000;;
let k = 100;;
let t = Array.init k (fun _ -> rd_union_find n);;
print_int !max_rang;;
print_newline ();;


(*
On trouve max rang <= 8.
C'est normal. La hauteur est en O(alpha(n)) (amortie). C'est optimal, on ne peut pas avoir une meilleur complexité pour ce problème.
On peut montrer que avec uniquement l'union par rang la hauteur est en O(log(n)).
*)

