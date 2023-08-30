let rec reduction_asc a p =
  if fless p a then reduction_asc a (p +. p) else p
  in
let rec reduction_dec a p pi2 =
  if fless pi2 a then
    let q = fhalf p in
    if fless p a then
      reduction_dec (a -. p) q pi2
    else
      reduction_dec a q pi2
  else a
  in
let rec reduction a pi2 =
  let p = reduction_asc a (pi2 +. pi2) in
  reduction_dec a p pi2
  in

let rec sin x =
  let pi = 3.141592653 in
  let abs = fabs x in
  let a = if fless 6.283185306 abs then reduction abs 6.283185306 else abs in
  let sign2 = pi -. a in
  let a = fabs sign2 in
  let pi_half = 1.570796326 in
  let sign = fsgnjx x sign2 in
  let a = pi_half -. fabs (a -. pi_half) in
  if fless a 0.78539816325 then
    let x = a in
    (* kernel-sin *)
    let xx = x *. x in
    let s = x *. (1.0 +. xx *. (-0.16666668 +. xx *. (0.008332824 +. xx *. -0.00019587841))) in
    fsgnj s sign
  else
    let x = pi_half -. a in
    (* kernel-cos *)
    let xx = x *. x in
    let c = 1.0 +. xx *. (-0.5 +. xx *. (0.04166368 +. xx *. -0.0013695068)) in
    fsgnj c sign
  in

let rec cos x =
  let pi = 3.141592653 in
  let abs = fabs x in
  let a = if fless 6.283185306 abs then reduction abs 6.283185306 else abs in
  let a = pi -. a in
  let pi_half = 1.570796326 in
  let a = fabs a in
  let sign = a -. pi_half in
  let a = fabs sign in
  if fless a 0.78539816325 then
    let x = a in
    (* kernel-sin *)
    let xx = x *. x in
    let s = x *. (1.0 +. xx *. (-0.16666668 +. xx *. (0.008332824 +. xx *. -0.00019587841))) in
    fsgnj s sign
  else
    let x = pi_half -. a in
    (* kernel-cos *)
    let xx = x *. x in
    let c = 1.0 +. xx *. (-0.5 +. xx *. (0.04166368 +. xx *. -0.0013695068)) in
    fsgnj c sign
  in

let rec atan sign =
  let abs = fabs sign in
  if fless abs 0.4375 then
    let x = sign in
    (* kernel-atan *)
    let xx = x *. x in
    let a = x *. (1.0 +. xx *. (-0.3333333 +. xx *. (0.2 +. xx *. (-0.142857142 +. xx *. (0.111111104 +. xx *. (-0.08976446 +. xx *. 0.060035485)))))) in
    a
  else if fless abs 2.4375 then
    let x = (abs -. 1.0) /. (abs +. 1.0) in
    (* kernel-atan *)
    let xx = x *. x in
    let a = x *. (1.0 +. xx *. (-0.3333333 +. xx *. (0.2 +. xx *. (-0.142857142 +. xx *. (0.111111104 +. xx *. (-0.08976446 +. xx *. 0.060035485)))))) in
    let a = 0.78539816325 +. a in
    fsgnj a sign
  else (
    let x = 1. /. abs in
    (* kernel-atan *)
    let xx = x *. x in
    let a = x *. (1.0 +. xx *. (-0.3333333 +. xx *. (0.2 +. xx *. (-0.142857142 +. xx *. (0.111111104 +. xx *. (-0.08976446 +. xx *. 0.060035485)))))) in
    let a = 1.570796326 -. a in
    fsgnj a sign
  ) in
