"""Record widths from Rocq types, without guessing from values."""
import re

WIDTH_MARKER = "CHAIN-MEMORY-WIDTH"
TRACE_WIDTH_MARKER = "CHAIN-TRACE-WIDTH"
ADDRESS_WIDTH_MARKER = "BOUNDARY-ADDRESS-WIDTH"
PRINT_MEMORY_WIDTHS = f'''all: try (iMatchHyp ltac:(fun H resource =>
  first [lazymatch resource with
    | @mem_mapsto _ _ ?width ?address _ _ =>
        try (lazymatch address with
          | context[@bv_unsigned ?addressWidth ?value] =>
            let addressWidth := eval vm_compute in addressWidth in
            idtac "{ADDRESS_WIDTH_MARKER}" value ":" addressWidth
          end);
        let width := eval vm_compute in width in
        idtac "{WIDTH_MARKER}" address ":" width
    end
  | lazymatch resource with
    | @mem_mapsto_array _ _ ?width ?address _ _ =>
        try (lazymatch address with
          | context[@bv_unsigned ?addressWidth ?value] =>
            let addressWidth := eval vm_compute in addressWidth in
            idtac "{ADDRESS_WIDTH_MARKER}" value ":" addressWidth
          end);
        let width := eval vm_compute in width in
        idtac "{WIDTH_MARKER}" address ":" width
    end
  | lazymatch resource with
    | spec_trace ?trace =>
        let rec events trace := lazymatch trace with
          | scons (SWriteMem ?address ?value) ?rest =>
              let width := eval vm_compute in (bvn_n value) in
              idtac "{TRACE_WIDTH_MARKER}" address ":" width; events rest
          | scons_snap (SWriteMem ?address ?value) _ ?rest =>
              let width := eval vm_compute in (bvn_n value) in
              idtac "{TRACE_WIDTH_MARKER}" address ":" width; events rest
          | _ => idtac
          end in events trace
    end]; fail)).'''


def captured_widths(text, marker):
    widths = {}
    for address, width in re.findall(rf"{marker}\s+([^\n]+?)\s*:\s*(\d+)(?:%N)?\b", text):
        width = int(width)
        if address in widths and widths[address] != width:
            raise ValueError(f"conflicting captured widths: {address}")
        widths[address] = width
    return widths
