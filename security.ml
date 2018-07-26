module Label = struct
  type t =
    | L of string

  let compare = compare

  let equal l1 l2 = compare l1 l2 = 0

  let hash = Hashtbl.hash

  let to_string (L s) = "#@" ^ s

  let make s = L s
end

module LabelGraph = Graph.Persistent.Digraph.ConcreteBidirectional (Label)
module G = LabelGraph (* Shortcut name for convenience *)
module PathG = Graph.Path.Check (LabelGraph)
module TopoG = Graph.Topological.Make (LabelGraph)
module BoundsMap = Map.Make (struct
  type t = Label.t * Label.t
  let compare = compare
end)
module RepresentationMap = Map.Make (Label)
module ReverseRepresentationMap = Map.Make (struct
  type t = int list
  let compare = compare
end)

exception Not_a_lattice of string

type lattice =
  {
    lattice : G.t;
    least_upper_bounds : Label.t BoundsMap.t;
    greatest_lower_bounds : Label.t BoundsMap.t;
    top : Label.t;
    bottom : Label.t;
    labels : Label.t list;
    label_representations : int list RepresentationMap.t;
    reverse_label_representations : Label.t ReverseRepresentationMap.t
  }

let compute_lub l1 l2 lattice =
  let path_checker = PathG.create lattice in
  let exists_path = PathG.check_path path_checker in
  let ub = G.fold_vertex (fun v acc -> if exists_path l1 v && exists_path l2 v then v::acc else acc) lattice [] in
  let least w = List.fold_left (fun acc v -> acc && (w = v || exists_path w v)) true ub in
  let lub = List.filter (fun v -> least v) ub in
  if List.length lub = 1 then
    (l1, l2, List.hd lub)
  else
    Gen.report_error
      VarGen.no_pos
      (Printf.sprintf
        "Security labels do not form a lattice; no least upper bound exists for %s and %s"
        (Label.to_string l1)
        (Label.to_string l2)
      )

let compute_glb l1 l2 lattice =
  let path_checker = PathG.create lattice in
  let exists_path = PathG.check_path path_checker in
  let lb = G.fold_vertex (fun v acc -> if exists_path v l1 && exists_path v l2 then v::acc else acc) lattice [] in
  let great w = List.fold_left (fun acc v -> acc && (w = v || exists_path v w)) true lb in
  let glb = List.filter (fun v -> great v) lb in
  if List.length glb = 1 then
    (l1, l2, List.hd glb)
  else
    Gen.report_error
      VarGen.no_pos
      (Printf.sprintf
        "Security labels do not form a lattice; no greatest lower bound exists for %s and %s"
        (Label.to_string l1)
        (Label.to_string l2)
      )

let compute_all_lub lattice =
  G.fold_vertex
    (fun v1 lubs1 ->
      G.fold_vertex
        (fun v2 lubs2 ->
          if v1 <> v2 then compute_lub v1 v2 lattice :: lubs2 else (v1, v1, v1) :: lubs2
        )
        lattice
        []
      :: lubs1
    )
    lattice
    []
  |> List.flatten

let compute_all_glb lattice =
  G.fold_vertex
    (fun v1 lubs1 ->
      G.fold_vertex
        (fun v2 lubs2 ->
          if v1 <> v2 then compute_glb v1 v2 lattice :: lubs2 else (v1, v1, v1) :: lubs2
        )
        lattice
        []
      :: lubs1
    )
    lattice
    []
  |> List.flatten

let make_sec_lattice_representation lattice =
  let size = G.nb_vertex lattice in
  let path_checker = PathG.create lattice in
  let exists_path = PathG.check_path path_checker in
  let rec empty_label size = if size = 0 then [] else 0 :: (empty_label (size - 1)) in
  let rec next_label label index =
    if index = 0 then 1 :: (List.tl label) else (List.hd label) :: (next_label (List.tl label) (index - 1)) in
  let rec lub l1 l2 = match l1,l2 with
  | (0 :: r1, 0 :: r2)   -> 0 :: (lub r1 r2)
  | (_ :: r1, _ :: r2)   -> 1 :: (lub r1 r2)
  | ([], _) | (_, []) -> []
  in
  let rp =
    TopoG.fold
      (fun v (map, reverse_map) ->
        if RepresentationMap.is_empty map then
          let rep = empty_label size in
          RepresentationMap.add v rep map, ReverseRepresentationMap.add rep v reverse_map
        else
          let index = RepresentationMap.cardinal map - 1 in
          let label =
            RepresentationMap.fold
              (fun l l_rep v_rep ->
                if exists_path l v then
                  lub v_rep l_rep
                else
                  v_rep
              )
              map
              (empty_label size) in
          let rep = next_label label index in
          RepresentationMap.add v rep map, ReverseRepresentationMap.add rep v reverse_map
      )
      lattice
      (RepresentationMap.empty, ReverseRepresentationMap.empty) in
  (* let rp = TopoG.fold (fun v a ->
    if a = [] then [(v, empty_label size)] else
      let idx = (List.length a) - 1 in
      let lb  = List.fold_left (fun acc (vl,r) -> if exists_path vl v then (lub acc r) else acc) (empty_label size) a in
      (v, next_label lb idx) :: a
    ) lattice [] in *)
  rp

let make_lattice labels relations =
  if labels = [] then
    Gen.report_error VarGen.no_pos "Security lattice cannot be empty"
  else if relations = [] then
    Gen.report_error VarGen.no_pos "Security label relations cannot be empty"
  else
    let lattice =
      G.empty
      |> List.fold_right (fun lbl lattice -> G.add_vertex lattice lbl) labels
      |> List.fold_right (fun (l1, l2) lattice -> G.add_edge lattice l1 l2) relations
    in
    let lub_map =
      compute_all_lub lattice
      |> List.fold_left (fun lubs (l1, l2, lub) -> BoundsMap.add (l1, l2) lub lubs) BoundsMap.empty in
    let glb_map =
      compute_all_glb lattice
      |> List.fold_left (fun glbs (l1, l2, glb) -> BoundsMap.add (l1, l2) glb glbs) BoundsMap.empty in
    let representation_map, reverse_representation_map = make_sec_lattice_representation lattice in
    {
      lattice = lattice;
      least_upper_bounds = lub_map;
      greatest_lower_bounds = glb_map;
      labels;
      top = List.fold_left (fun acc v -> if G.out_degree lattice v = 0 then v else acc) (List.hd labels) (List.tl labels);
      bottom = List.fold_left (fun acc v -> if G.in_degree lattice v = 0 then v else acc) (List.hd labels) (List.tl labels);
      label_representations = representation_map;
      reverse_label_representations = reverse_representation_map
    }

let default_lattice =
  let lo = Label.make "Lo" in
  let hi = Label.make "Hi" in
  let rel = [(lo, hi)] in
  make_lattice [lo; hi] rel

let is_valid_security_label { lattice } l = G.mem_vertex lattice l

let get_top lattice = lattice.top
let get_bottom lattice = lattice.bottom

let get_representation { label_representations } label =
  RepresentationMap.find label label_representations

let representation_to_label { reverse_label_representations } representation =
  ReverseRepresentationMap.find representation reverse_label_representations

let least_upper_bound { least_upper_bounds } l1 l2 = BoundsMap.find (l1, l2) least_upper_bounds

let greatest_lower_bound { greatest_lower_bounds } l1 l2 = BoundsMap.find (l1, l2) greatest_lower_bounds

let current_lattice = ref default_lattice

let lattice_size { lattice } = G.nb_vertex lattice
