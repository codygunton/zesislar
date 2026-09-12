Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPayloadCall.

Ltac run_exact_header_call_until stop :=
  lazymatch goal with
  | |- instr_body ?address _ =>
      first [ constr_eq address stop
            | first
                [ progress iEval
                    (unfold zesuWriteOutputPayloadCallSpec, zesu_c_call)
                | liAStep
                | progress prepare_sidecond
                | reflexivity
                | vm_compute
                | bv_solve
                | lia ];
              run_exact_header_call_until stop ]
  | _ =>
      first
        [ progress iEval (unfold zesuWriteOutputPayloadCallSpec, zesu_c_call)
        | liAStep
        | progress prepare_sidecond
        | reflexivity
        | vm_compute
        | bv_solve
        | lia ];
      run_exact_header_call_until stop
  end.

Ltac run_exact_header_call :=
  lazymatch goal with
  | _ =>
      first
        [ progress iEval (unfold zesuWriteOutputPayloadCallSpec, zesu_c_call)
        | liAStep
        | progress prepare_sidecond
        | reflexivity
        | vm_compute
        | bv_solve
        | lia ];
      run_exact_header_call
  end.
