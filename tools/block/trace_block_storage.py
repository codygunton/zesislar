"""Bind completed storage receipts without changing any capture byte."""

import json
from pathlib import Path

from trace_block_seal import checked_reference, file_sha256


IDENTITY_LIMIT = "Installation-time symlink identities remain unavailable. Later identity observations do not reconstruct them."


def verify_storage_records(raw_root, records):
    """Bind every replaced raw path to its reviewed journal, mirror, and archive."""
    root = Path(raw_root).resolve(strict=True)
    links = {}
    for path in root.rglob("*"):
        if not path.is_symlink():
            continue
        if not path.is_file():
            raise ValueError("A raw link is broken or does not target a regular file: " + str(path))
        links[str(path.absolute())] = path
    if records is None:
        if links:
            raise ValueError("Raw file links require the completed storage records.")
        return None
    if isinstance(records, dict) and "restoration" in records:
        return verify_restoration_records(root, records, links)
    required = {"transfer_seal", "journal", "audit", "identity_observation"}
    if not isinstance(records, dict) or set(records) != required:
        raise ValueError("The completed storage record references are incomplete.")
    paths = {key: checked_reference(value) for key, value in records.items()}
    seal = json.loads(paths["transfer_seal"].read_text())
    audit = json.loads(paths["audit"].read_text())
    identity = records["identity_observation"]
    if (seal.get("result", {}).get("phase") != "complete"
            or seal.get("original_hashes_match") is not True
            or seal.get("archive_hashes_match") is not True):
        raise ValueError("The transfer seal does not establish a completed transfer.")
    references = {row["path"]: row["sha256"] for row in seal.get("references", [])}
    journal = records["journal"]
    if references.get(journal["path"]) != journal["sha256"]:
        raise ValueError("The transfer seal does not bind the exact journal.")
    for name in ("transfer_seal", "journal", "identity_observation"):
        reference = records[name]
        if audit.get("bindings", {}).get(reference["path"]) != reference["sha256"]:
            raise ValueError("The storage audit does not bind " + name + ".")
    for key in ("all_archive_hashes_match", "all_journal_transitions_match",
                "all_recorded_source_mirror_decompression_hashes_match",
                "all_recorded_targets_and_sizes_match"):
        if audit.get(key) is not True:
            raise ValueError("The completed storage audit lacks " + key + ".")
    supplement = audit.get("later_identity_supplement", {})
    if supplement.get("source") != identity["path"] or supplement.get("sha256") != identity["sha256"]:
        raise ValueError("The audit has a different later identity observation.")
    installed, completed = {}, None
    with paths["journal"].open() as stream:
        for line in stream:
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError("A storage journal row is not a map.")
            phase = row.get("phase")
            if completed is not None:
                raise ValueError("The storage journal contains work after completion.")
            if phase == "installed":
                name = row.get("original")
                if not isinstance(name, str) or name in installed:
                    raise ValueError("The storage journal has an invalid or duplicate installed path.")
                installed[name] = row
            elif phase == "complete":
                if completed is not None:
                    raise ValueError("The storage journal has duplicate completion records.")
                completed = row
            elif completed is not None:
                raise ValueError("The storage journal contains work after completion.")
    files = seal.get("files")
    if (not isinstance(files, list) or completed is None
            or type(completed.get("files")) is not int
            or type(seal["result"].get("files")) is not int
            or completed.get("files") != len(installed)
            or seal["result"].get("files") != len(installed)):
        raise ValueError("The storage journal and seal have different completion counts.")
    entries = {}
    for row in files:
        if not isinstance(row, dict):
            raise ValueError("A storage seal entry is not a map.")
        name = row.get("original")
        if not isinstance(name, str) or name in entries:
            raise ValueError("The storage seal has an invalid or duplicate original path.")
        entries[name] = row
    if set(entries) != set(installed):
        raise ValueError("The storage seal and journal have different installed paths.")
    matched = []
    for name, source in sorted(links.items()):
        entry, row = entries.get(name), installed.get(name)
        if entry is None or row is None:
            raise ValueError("A raw file link has no installed storage record: " + name)
        for field, journal_field in (("sha256", "original_sha256"), ("mirror", "mirror"),
                ("archive", "archive"), ("archive_sha256", "archive_sha256"),
                ("original_bytes", "original_bytes"), ("archive_bytes", "archive_bytes")):
            if entry.get(field) != row.get(journal_field):
                raise ValueError("The storage journal and seal disagree on " + field + ".")
        if (row.get("decompression_equal") is not True
                or row.get("decompressed_sha256") != entry["sha256"]
                or row.get("mirror_sha256") != entry["sha256"]):
            raise ValueError("The installed storage record lacks its recorded byte comparison.")
        mirror = checked_reference({"path": entry["mirror"], "sha256": entry["sha256"]})
        archive = checked_reference({"path": entry["archive"], "sha256": entry["archive_sha256"]})
        if source.resolve(strict=True) != mirror.resolve(strict=True):
            raise ValueError("A raw file link has a different mirror target.")
        if (str(source.readlink()) != row.get("symlink_target")
                or row.get("symlink_target") != str(mirror)
                or row.get("resolved") != str(mirror.resolve(strict=True))):
            raise ValueError("The installed storage target differs from the actual mirror.")
        if (type(entry.get("original_bytes")) is not int
                or source.stat().st_size != entry["original_bytes"]
                or type(entry.get("archive_bytes")) is not int
                or archive.stat().st_size != entry["archive_bytes"]):
            raise ValueError("A storage mirror or archive has a different size.")
        if file_sha256(source) != entry["sha256"]:
            raise ValueError("The original raw path has different bytes.")
        matched.append({"original": name, "mirror": str(mirror), "sha256": entry["sha256"],
                        "archive": str(archive), "archive_sha256": entry["archive_sha256"]})
    return {"records": records, "verified_replacements": matched,
            "replacement_scope": "This raw root only. The shared receipt also binds the other transferred roots.",
            "installation_time_identity": "unavailable", "identity_limit": IDENTITY_LIMIT,
            "audit_limits": audit.get("limits", []), "journal_gap": audit.get("journal_gap"),
            "archive_verification": "Current archive hashes and recorded byte comparisons. No new decompression ran."}


def verify_restoration_records(root, records, links):
    """Verify regular originals against the restoration and archived history."""
    if set(records) != {"restoration", "archived_metadata"}:
        raise ValueError("The restoration record references are incomplete.")
    if links:
        raise ValueError("Restored raw evidence still contains file links.")
    receipt_path = checked_reference(records["restoration"])
    receipt = json.loads(receipt_path.read_text())
    metadata = records["archived_metadata"]
    roles = {"transfer_seal", "journal", "audit", "identity_observation"}
    optional_roles = {"transfer_result", "monitor_redirect"}
    if (not isinstance(metadata, dict) or not roles.issubset(metadata)
            or not set(metadata).issubset(roles | optional_roles)):
        raise ValueError("The archived storage metadata references are incomplete.")
    if (type(receipt.get("schema")) is not int or receipt["schema"] != 1 or receipt.get("status") != "complete"
            or receipt.get("mirror_root_removed") is not True
            or type(receipt.get("proof_source_changes")) is not int
            or receipt["proof_source_changes"] != 0
            or receipt.get("archived_metadata") != metadata):
        raise ValueError("The restoration receipt is incomplete or differs from its metadata.")
    reversal_journal = receipt.get("reversal_journal")
    checked_reference(reversal_journal)
    paths = {}
    for role, reference in metadata.items():
        if (not isinstance(reference, dict) or set(reference) != {"path", "sha256", "original_path"}
                or not isinstance(reference["original_path"], str)
                or not Path(reference["original_path"]).is_absolute()):
            raise ValueError("An archived storage reference is malformed.")
        paths[role] = checked_reference(reference)
    seal = json.loads(paths["transfer_seal"].read_text())
    audit = json.loads(paths["audit"].read_text())
    if (seal.get("result", {}).get("phase") != "complete"
            or seal.get("original_hashes_match") is not True
            or seal.get("archive_hashes_match") is not True):
        raise ValueError("The archived transfer seal is incomplete.")
    if "transfer_result" in metadata:
        result_reference = metadata["transfer_result"]
        references = {row["path"]: row["sha256"] for row in seal.get("references", [])}
        if references.get(result_reference["original_path"]) != result_reference["sha256"]:
            raise ValueError("The archived transfer seal does not bind its result bytes.")
        transfer_result = json.loads(paths["transfer_result"].read_text())
        if transfer_result.get("phase") != "complete":
            raise ValueError("The archived transfer result is incomplete.")
    if "monitor_redirect" in metadata:
        redirect = json.loads(paths["monitor_redirect"].read_text())
        parent = redirect.get("physical_output_parent")
        raw_seals = redirect.get("raw_seals")
        if (not isinstance(parent, str) or not Path(parent).is_absolute()
                or not isinstance(raw_seals, dict) or not raw_seals
                or type(redirect.get("proof_changes")) is not int or redirect["proof_changes"] != 0
                or type(redirect.get("signals")) is not int or redirect["signals"] != 0
                or any(not isinstance(path, str) or not Path(path).is_absolute()
                       or not Path(path).is_relative_to(Path(parent)) for path in raw_seals.values())):
            raise ValueError("The archived monitor redirect has invalid output paths or mutations.")
    journal_reference = metadata["journal"]
    seal_refs = {row["path"]: row["sha256"] for row in seal.get("references", [])}
    if seal_refs.get(journal_reference["original_path"]) != journal_reference["sha256"]:
        raise ValueError("The archived transfer seal does not bind the journal bytes.")
    for role in ("transfer_seal", "journal", "identity_observation"):
        reference = metadata[role]
        if audit.get("bindings", {}).get(reference["original_path"]) != reference["sha256"]:
            raise ValueError("The archived audit does not bind " + role + ".")
    identity = metadata["identity_observation"]
    supplement = audit.get("later_identity_supplement", {})
    if (supplement.get("source") != identity["original_path"]
            or supplement.get("sha256") != identity["sha256"]):
        raise ValueError("The archived audit has a different identity observation.")
    for key in ("all_archive_hashes_match", "all_journal_transitions_match",
                "all_recorded_source_mirror_decompression_hashes_match",
                "all_recorded_targets_and_sizes_match"):
        if audit.get(key) is not True:
            raise ValueError("The archived audit lacks " + key + ".")
    mirror_root = receipt.get("mirror_root")
    if not isinstance(mirror_root, str) or not Path(mirror_root).is_absolute():
        raise ValueError("The restoration receipt has an invalid old mirror root.")
    if Path(mirror_root).exists() or Path(mirror_root).is_symlink():
        raise ValueError("The receipt's removed mirror root still exists.")
    originals = {}
    for row in seal.get("files", []):
        if not isinstance(row, dict) or not isinstance(row.get("original"), str):
            raise ValueError("The archived transfer seal has an invalid original.")
        if row["original"] in originals:
            raise ValueError("The archived transfer seal repeats an original.")
        originals[row["original"]] = row
    restored = {}
    for row in receipt.get("restored_files", []):
        if not isinstance(row, dict) or not isinstance(row.get("original"), str):
            raise ValueError("The restoration receipt has an invalid original.")
        name = row["original"]
        if not Path(name).is_absolute() or name in restored:
            raise ValueError("The restoration receipt repeats or misnames an original.")
        restored[name] = row
    if (not originals or set(restored) != set(originals)
            or type(seal.get("result", {}).get("files")) is not int
            or seal["result"]["files"] != len(restored)):
        raise ValueError("The restoration and archived transfer have different original sets.")
    if "transfer_result" in metadata:
        if (type(transfer_result.get("files")) is not int
                or transfer_result["files"] != len(restored)):
            raise ValueError("The archived transfer result has a different file count.")
    verified = []
    for name, row in sorted(restored.items()):
        previous = originals[name]
        archive = row.get("archive")
        if (row.get("sha256") != previous.get("sha256")
                or type(row.get("bytes")) is not int or row["bytes"] != previous.get("original_bytes")
                or row.get("regular_file") is not True or row.get("symlink") is not False
                or row.get("mirror_removed") is not True or row.get("old_mirror") != previous.get("mirror")
                or not isinstance(archive, dict) or archive.get("disposition") != "retained-on-home"
                or archive.get("path") != previous.get("archive")
                or archive.get("sha256") != previous.get("archive_sha256")
                or type(archive.get("bytes")) is not int or archive["bytes"] != previous.get("archive_bytes")):
            raise ValueError("A restored entry differs from its archived transfer identity.")
        if (not isinstance(row.get("old_mirror"), str)
                or not Path(row["old_mirror"]).is_relative_to(Path(mirror_root))):
            raise ValueError("A restored entry names a mirror outside the removed root.")
        source = Path(name)
        if not source.is_relative_to(root):
            continue
        if source.is_symlink() or not source.is_file():
            raise ValueError("A restored original is not a regular file: " + name)
        checked_reference({"path": name, "sha256": row["sha256"]})
        if source.stat().st_size != row["bytes"]:
            raise ValueError("A restored original has a different size.")
        archive_path = checked_reference(archive)
        if archive_path.stat().st_size != archive["bytes"]:
            raise ValueError("A retained archive has a different size.")
        verified.append({"original": name, "sha256": row["sha256"], "bytes": row["bytes"],
                         "current_type": "regular-file", "archive": archive})
    return {"mode": "restored-originals", "records": records,
            "reversal_journal": reversal_journal,
            "verified_restorations": verified,
            "verification_scope": "Current originals and archives in this raw root. Other roots remain receipt-bound.",
            "historical_mirrors": "Removed. Old mirror paths remain historical metadata only.",
            "installation_time_identity": "unavailable", "identity_limit": IDENTITY_LIMIT,
            "audit_limits": audit.get("limits", []), "journal_gap": audit.get("journal_gap"),
            "archive_verification": "Current archive hashes and recorded byte comparisons. No new decompression ran."}
