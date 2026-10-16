exception Exhausted
let configured ()=Sys.getenv_opt "ZESU_TRACE_RAW_BUDGET"
let with_output path emit =
  match configured()with
  |None->
      let channel=open_out_gen[Open_wronly;Open_creat;Open_excl;Open_binary]0o600 path in
      Fun.protect ~finally:(fun()->close_out_noerr channel)(fun()->let value=emit channel in flush channel;value)
  |Some ledger->
      let helper=match Sys.getenv_opt "ZESU_TRACE_RAW_BUDGET_WRITER"with
        |Some path->path|None->failwith "The raw budget sink is unavailable"in
      let read_input,write_input=Unix.pipe ~cloexec:true()in
      let null=Unix.openfile "/dev/null"[Unix.O_WRONLY;Unix.O_CLOEXEC]0 in
      let pid=try Fun.protect ~finally:(fun()->Unix.close read_input;Unix.close null)(fun()->
        Unix.create_process "/usr/bin/python3"[|"/usr/bin/python3";helper;"--ledger";ledger;"--destination";path|]
          read_input null null)with error->Unix.close write_input;raise error in
      let channel=Unix.out_channel_of_descr write_input in
      let result=try let value=emit channel in flush channel;Ok value with error->Error error in
      close_out_noerr channel;
      let rec wait()=try snd(Unix.waitpid[]pid)with Unix.Unix_error(Unix.EINTR,_,_)->wait()in
      let status=wait()in
      (match result with Error error when not(CErrors.noncritical error)->raise error|_->());
      if status=Unix.WEXITED 75 then raise Exhausted;
      (match result,status with Error error,_->raise error|Ok value,Unix.WEXITED 0->value
       |_->failwith "The raw budget sink failed")
let status ()=
  match configured()with
  |None->`Null
  |Some path->
      let descriptor=Unix.openfile path[Unix.O_RDWR;Unix.O_CLOEXEC]0 in
      Fun.protect ~finally:(fun()->Unix.close descriptor)(fun()->
        Unix.lockf descriptor Unix.F_LOCK 0;
        let channel=Unix.in_channel_of_descr(Unix.dup ~cloexec:true descriptor)in
        let value=Fun.protect ~finally:(fun()->close_in channel)(fun()->Yojson.Safe.from_channel channel)in
        let fields=match value with `Assoc fields->fields|_->failwith "Invalid raw ledger"in
        `Assoc["schema",`Int 1;"limit_bytes",List.assoc "limit_bytes"fields;
          "limit_reached",`Bool(List.assoc "complete"fields<>`Bool true);
          "ledger",`String "evidence/RAW-BUDGET.json"])

let ensure_data ()=match status()with
  |`Assoc fields when List.assoc "limit_reached"fields=`Bool true->raise Exhausted
  |_->()
