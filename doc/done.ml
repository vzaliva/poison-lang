(* Drone dual control system.

The posistion control is independent from the altitude control.
And we can show that faulty barometer does not affect the position control.
*)

let land_thresh = 50.0 (* m *)

let descent_time = 10.0 (* s *)

let read_barometer () =
  if Random.int 10 < 3 then (* 30% failure probability *)
    -1.0
  else
    10.0 +. float_of_int (Random.int 120)


(* 10-129 m *)

let read_user_land () = Random.bool () (* flip a coin for demo *)

let read_user_control pos =
  (* Simulate user providing new lateral position
     pos: distance in meters from central divider (negative = left, positive = right) *)
  let adjustment = Random.float 2.0 -. 1.0 in
  (* -1.0 to 1.0 meters *)
  pos +. adjustment


let descent_rate alt = alt /. descent_time

let maintain_altitude () = print_endline "[ALT] maintaining altitude"

let initiate_landing alt =
  Printf.printf "[ALT] LAND from %.1f m  (%.1f m/s)\n" alt (descent_rate alt)


let hold_position pos =
  (* pos: distance in meters from central divider *)
  Printf.printf "[LAT] holding position %.1f m from center\n" pos


let altitude_control user_land alt =
  if user_land && alt < land_thresh then
    initiate_landing alt (* may consume poisoned value *)
  else
    maintain_altitude () (* independent of alt when user_land = false *)


let rec main_rec n target_pos =
  if n >= 10 then
    ()
  else (
    let altitude = read_barometer () in
    (* error unchecked → poison *)
    let user_land = read_user_land () in
    (* external command *)
    altitude_control user_land altitude;
    (* affected iff user_land=true *)
    hold_position target_pos;
    (* Get new target position from user *)
    let new_target = read_user_control target_pos in
    Unix.sleep 1;
    main_rec (n + 1) new_target)


let () =
  Random.self_init ();
  main_rec 0 0.0
