open Printf

let ssqrs (a, b, c, d) = a * a + b * b + c * c + d * d

let print4 (a, b, c, d) = printf "%d=%d²+%d²+%d²+%d²\n" (ssqrs (a, b, c, d)) a b c d

let map4 f (a, b, c, d) = (f a, f b, f c, f d)

let div4 xi m = map4 (fun x -> x / m) xi
let mod4 xi m = map4 (fun x -> x mod m) xi

let boption f a = if f a then Some () else None

let euler (a, b, c, d) (w, x, y, z) =
  abs (a*w + b*x + c*y + d*z),
  abs (a*x - b*w - c*z + d*y),
  abs (a*y + b*z - c*w - d*x),
  abs (a*z - b*y + c*x - d*w)

let rec find a b f =
  if a > b then None else
    match f a with
      | Some y -> Some (a, y)
      | None -> find (a + 1) b f

let bfind a b f = find a b (boption f)

let run s = function
  | Some a -> a
  | None -> failwith (s ^" run : some not found")

let prime2 p =
  let (l, (m, ())) =
    run ("prime2 " ^ string_of_int p)
      (find 0 ((p - 1) / 2) (fun l ->
        bfind 0 ((p - 1) / 2) (fun m ->
	  (1 + l * l + m * m) mod p = 0)))
  in (l, m)

(* Case analysis for n <= 3 *)
let small_lagrange n =
  if n < 0 || n > 4 then invalid_arg "small_lagrange" else
  map4 (min 1) (map4 ((/) n) (4, 3, 2, 1))

let prime4_multiple p =
  if p <= 2 then
    (1, small_lagrange p)
  else
    let (l, m) = prime2 p in
    let k = (1 + l * l + m * m) / p in
    if (k >= p) then failwith "RHOOO BEN QUAND MÊME";
    (k, (0, 1, l, m))

let modsym m x =
  let y = x mod m in
  if y * 2 > m then y - m else y

let rec prime4_demultiplie p (m, xi) =
  if m = 1 then xi else
  let yi = map4 (modsym m) xi in
  prime4_demultiplie p (ssqrs yi / m, div4 (euler xi yi) m)

let prime4 p = prime4_demultiplie p (prime4_multiple p)

let factor =
  let primes = [2; 3; 5; 7; 11; 13; 17; 19] in
  let rec findfact x = function
    | [] -> None
    | p :: ps when p > x -> failwith "wrong primes"
    | p :: ps -> if x mod p = 0 then Some (p, x / p) else findfact x ps
  in fun x ->
    if x = 1 then failwith "nope, I won't factor 1." else
    findfact x primes

let rec lagrange n =
  if n <= 4 then
    small_lagrange n
  else
    match factor n with
      | Some (p, n) -> euler (prime4 p) (lagrange n)
      | None ->
          let xi = prime4 n in
          if ssqrs xi = n then xi else
            failwith (sprintf "Wrong factorisation. Hopefully it's because %d is composite or is too big" n)

let () =
  print4 (lagrange 3100);
  (*print4 (lagrange 67063);*)
  let bound = if Array.length Sys.argv >= 2 then int_of_string Sys.argv.(1) else 20 in
  for n = 0 to bound do
    try
      let xi = lagrange n in
      if ssqrs xi <> n then failwith ("FAIL with n=" ^ string_of_int n);
      print4 xi;
    with
      | Failure s -> printf "\tFAILURE (%s)\n" s
      | Assert_failure _ -> printf "\tASSERT FAILURE\n"
  done















