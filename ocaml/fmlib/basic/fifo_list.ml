type 'a t = {
    front: 'a list;
    rear:  'a list;
}


let empty: 'a t =
    {front = []; rear = [];}


let push_front (e: 'a) (fifo: 'a t): 'a t =
    {fifo with front = e :: fifo.front}


let push_rear (e: 'a) (fifo: 'a t): 'a t =
    {fifo with rear = e :: fifo.rear}


let pop_front (fifo: 'a t): ('a * 'a t) option =
    match fifo.front with
    | hd :: front ->
        Some (hd, {fifo with front})

    | [] ->
        match List.rev fifo.rear with
        | [] ->
            None

        | hd :: front ->
            Some (hd, {front; rear = []})
