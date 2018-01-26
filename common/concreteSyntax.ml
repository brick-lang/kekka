module TypeBinder = struct
  type 'a t = {
    name : Name.t;
    kind : 'a;
    (* name_range : Range.t;
     * range : Range.t; *)
  }
end
