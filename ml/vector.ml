type 'a t = {
    mutable array: 'a Array.t;
    mutable size : int
}

let init () : 'a t = {array = [||]; size = 0}

let increase_size (v: 'a t) (a:'a) : unit =
    begin
        let new_array = Array.make (2 * (Array.length v.array) + 1) a in

        for i=0 to v.size - 1 do
            new_array.(i) <- v.array.(i)
        done;

        v.array <- new_array
    end

let decrease_size (v: 'a t) : unit =
    begin
        let new_array = if v.size = 0 then [||] else 
            Array.make v.size v.array.(0)
        in

        for i=0 to v.size do
            new_array.(i) <- v.array.(i)
        done;

        v.array <- new_array
    end

let length (v:'a t) : int = v.size

let push (v:'a t) (a:'a) =
    begin
        if Array.length v.array < v.size + 1 then increase_size v a;
        Array.set v.array v.size a;
        v.size <- v.size + 1
    end

let get (v:'a t) (i:int) : 'a = 
    begin
        assert (0 <= i && i < v.size);
        v.array.(i)
    end

let set (v:'a t) (i:int) (a:'a) : unit = 
    begin
        assert (0 <= i && i < v.size);
        v.array.(i) <- a 
    end


let pop (v:'a t) : 'a option = if v.size = 0 then None else
    begin
        let x = get v (v.size-1) in
        v.size <- v.size - 1;

        if Array.length v.array > 2 * v.size then decrease_size v;

        Some x
    end

let iter (v: 'a t) (f: 'a -> unit) : unit = 
    begin
        for i=0 to v.size-1 do f (get v i) done
    end

let iteri (v: 'a t) (f: int -> 'a -> unit) : unit = 
    begin
        for i=0 to v.size-1 do f i (get v i) done
    end

let map (v:'a t) (f: 'a -> 'b) : 'b t =
    match v.size with
    | 0 -> 
        init ()
    | s -> 
        begin
            let array = Array.make s (f v.array.(0)) in

            for i=1 to v.size-1 do
                array.(i) <- f v.array.(i);
            done;

            {
                array= array; size= v.size
            }


        end