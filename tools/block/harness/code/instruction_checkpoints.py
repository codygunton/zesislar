"""Report authorized PORT instruction counters without controlling jobs."""
import csv
import hashlib
import json
import math
import os
from pathlib import Path
import tempfile
import time

from perf_measure import parse_stat
from port_native_policy import port_case

INTERVAL_CPU_SECONDS = 600
LONG_SEARCH_CPU_SECONDS = 21600

SCOPE = 'Full MCP session and inherited descendants; not search-only.'
MAX_LINE_BYTES = 8192
READ_BYTES = 65536


def atomic(path, value):
    path = Path(path)
    temporary = path.with_suffix(path.suffix + '.pending')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def create_once(path, value):
    """Publish one complete report without replacing an existing report."""
    path = Path(path)
    fd, name = tempfile.mkstemp(prefix=path.name + '.', suffix='.pending', dir=path.parent)
    try:
        with os.fdopen(fd, 'w') as stream:
            stream.write(json.dumps(value, indent=2) + '\n')
        try:
            os.link(name, path)
            return True
        except FileExistsError:
            return False
    finally:
        Path(name).unlink(missing_ok=True)


class Counter:
    def __init__(self,path):
        self.path=Path(path);self.offset=0;self.identity=None
        self.partial=b'';self.partial_length=0;self.partial_hash=hashlib.sha256()
        self.line_start=0;self.line_number=0;self.unread_bytes=0
        self.total=0;self.prefix_total=0;self.prefix_intervals=0;self.intervals=0
        self.interval_end=None;self.high_water_end=None;self.next_start=0.0
        self.failure=None;self.failure_detail=None;self.file_state='missing'
        self.observed_ns=None;self.poll_ns=None
        self.records=[];self.gaps=[];self.segments=[];self.segment_open=False

    def _gap(self,reason,record):
        gap=dict(record,kind='gap',reason=reason,user_instructions=None)
        self.gaps.append(gap);self.records.append(gap);self.segment_open=False

    def _line(self,raw,raw_length,raw_sha256,end_offset,now_ns):
        self.line_number+=1
        record={'line':self.line_number,'byte_start':self.line_start,'byte_end':end_offset,
                'raw_sha256':raw_sha256,'raw_bytes':raw_length,
                'raw_line':raw.decode('ascii',errors='replace')}
        if raw_length>MAX_LINE_BYTES:
            self._gap('counter_line_too_long',record);self.next_start=None;return
        try:text=raw.decode('ascii').strip()
        except UnicodeError:
            self._gap('counter_non_ascii',record);self.next_start=None;return
        if not text or text.startswith('#'):return
        endpoint=None;timestamp_accepted=False
        try:
            fields=next(csv.reader([text],strict=True))
            if len(fields)<6:raise ValueError('counter_columns_invalid')
            endpoint=float(fields[0])
            if not math.isfinite(endpoint) or endpoint<=0:
                raise ValueError('counter_timestamp_invalid')
            if self.high_water_end is not None and endpoint<=self.high_water_end:
                raise ValueError('counter_interval_not_increasing')
            self.high_water_end=endpoint
            timestamp_accepted=True
            record['perf_interval_end_seconds']=endpoint
            record['perf_interval_start_seconds']=self.next_start
            validated=fields[1:]
            zero=validated[0].strip()=='0'
            if zero:validated[0]='1'
            parsed=parse_stat(','.join(validated))
            if zero:parsed['user_instructions']=0
        except (ValueError,csv.Error,StopIteration) as error:
            self._gap(str(error),record)
            self.next_start=endpoint if timestamp_accepted else None
            return
        value=dict(record,kind='valid',**parsed)
        self.records.append(value);self.total+=parsed['user_instructions'];self.intervals+=1
        if not self.gaps:
            self.prefix_total+=parsed['user_instructions'];self.prefix_intervals+=1
        if not self.segment_open:
            self.segments.append({'first_line':self.line_number,'last_line':self.line_number,
                'perf_interval_start_seconds':self.next_start,'perf_interval_end_seconds':endpoint,
                'intervals':1,'user_instructions':parsed['user_instructions'],'scope':SCOPE})
            self.segment_open=True
        else:
            segment=self.segments[-1];segment['last_line']=self.line_number
            segment['perf_interval_end_seconds']=endpoint;segment['intervals']+=1
            segment['user_instructions']+=parsed['user_instructions']
        self.interval_end=endpoint;self.next_start=endpoint;self.observed_ns=now_ns

    def _consume(self,data,now_ns):
        parts=data.split(b'\n')
        for index,part in enumerate(parts):
            self.partial_hash.update(part);self.partial_length+=len(part)
            if len(self.partial)<MAX_LINE_BYTES:
                self.partial+=part[:MAX_LINE_BYTES-len(self.partial)]
            if index==len(parts)-1:continue
            end=self.line_start+self.partial_length+1
            self._line(self.partial,self.partial_length,self.partial_hash.hexdigest(),end,now_ns)
            self.line_start=end;self.partial=b'';self.partial_length=0
            self.partial_hash=hashlib.sha256()

    def poll(self,now_ns):
        self.poll_ns=now_ns
        if self.failure:return
        try:
            try:stream=self.path.open('rb')
            except FileNotFoundError:
                if self.identity is None:self.file_state='missing';return
                raise ValueError('counter_file_missing_after_open')
            with stream:
                info=os.fstat(stream.fileno());identity=(info.st_dev,info.st_ino)
                if self.identity is not None and identity!=self.identity:
                    raise ValueError('counter_file_replaced')
                if info.st_size<self.offset:raise ValueError('counter_file_shrank')
                self.identity=identity;stream.seek(self.offset);data=stream.read(READ_BYTES)
                self.offset+=len(data)
                after=os.fstat(stream.fileno())
                if after.st_size<self.offset:raise ValueError('counter_file_shrank_during_read')
            current=self.path.stat()
            if (current.st_dev,current.st_ino)!=self.identity:raise ValueError('counter_file_replaced_during_read')
            self.unread_bytes=max(0,current.st_size-self.offset)
            self._consume(data,now_ns);self.file_state='present'
        except (OSError,ValueError) as error:
            self.failure='counter_source_integrity_failure';self.failure_detail=str(error)
            self.file_state='invalid';self.records.append({'kind':'source_error',
                'reason':self.failure_detail,'offset':self.offset})

    def snapshot(self):
        reason=self.failure
        if reason is None:
            if self.file_state=='missing':reason='counter_file_missing'
            elif self.gaps:reason='counter_gaps'
            elif self.partial_length:reason='counter_partial_line'
            elif self.unread_bytes:reason='counter_unread_intervals'
            elif not self.intervals:reason='counter_unavailable'
        complete=self.total if self.intervals and reason is None else None
        return {'instructions':complete,'complete_observed_prefix_instructions':complete,
            'instructions_qualification':'Complete CSV-interval prefix only; not a CPU checkpoint or final session total.',
            'validated_prefix_instructions':self.prefix_total if self.prefix_intervals else None,
            'observed_valid_interval_sum':self.total if self.intervals else None,
            'observed_sum_qualification':'Exact sum of recorded valid intervals. Missing intervals remain unknown.',
            'full_session_total_instructions':None,'exact_checkpoint_instructions':None,
            'checkpoint_clock_alignment':'not proved','search_only':False,'scope':SCOPE,
            'valid_segments':[dict(row) for row in self.segments],
            'gaps':[dict(row) for row in self.gaps],'gap_count':len(self.gaps),
            'intervals':self.intervals,'perf_interval_end_seconds':self.interval_end,
            'failure':reason,'failure_detail':self.failure_detail,'file_state':self.file_state,
            'source_integrity_valid':self.failure is None,
            'observed_ns':self.observed_ns,'poll_ns':self.poll_ns,
            'partial_bytes':self.partial_length,'unread_bytes':self.unread_bytes,
            'complete_line_prefix_bytes':self.line_start,'read_offset_bytes':self.offset,
            'raw_counter_path':str(self.path),'source_identity':self.identity}


class Observer:
    def __init__(self, output, memory_job):
        # The shared policy owns authorization. Invalid PORT jobs retain its refusal.
        self.case = port_case(memory_job)
        self.output = Path(output)
        self.directory = self.output / 'native/instruction-profile'
        self.counter = Counter(self.directory / 'perf-stat.csv')
        self.last_before_origin = None
        self.baseline = None
        self.origin_ns = None
        self.rows = []
        self.next_threshold = INTERVAL_CPU_SECONDS
        self.enabled = self.case is not None
        self.max_search_cpu = None

    def sample(self, sample, now_ns=None):
        """Reporting failures do not change job admission, limits, or signals."""
        if self.case is None:
            return
        try:
            now_ns = time.time_ns() if now_ns is None else now_ns
            origin = sample.get('origin_cpu')
            cpu = sample.get('search_CPU_seconds')
            has_clock = (origin is not None or (type(cpu) in (int, float)
                         and math.isfinite(cpu) and cpu > 0))
            marker = self.directory / 'PROFILE-ACTIVE.json'
            failure = None
            unavailable = self.directory / 'PROFILE-UNAVAILABLE.json'
            if unavailable.exists():
                failure = 'profile_preparation_failed'
            elif not marker.exists():
                if not has_clock:
                    return
                failure = 'profile_marker_missing'
            else:
                active = json.loads(marker.read_text())
                if (not isinstance(active, dict)
                        or active.get('case') != self.case
                        or active.get('block') != self.case['block']
                        or active.get('interval_ms') != 1000):
                    failure = 'profile_marker_invalid'
            if failure is None:
                self.counter.poll(now_ns)
                snapshot = self.counter.snapshot()
            else:
                snapshot = dict(instructions=None, failure=failure,
                                raw_counter_path=str(self.counter.path))
            if not has_clock:
                self.last_before_origin = snapshot
                return
            if self.origin_ns is None:
                origin_path = self.output / 'SEARCH-CPU-ORIGIN.json'
                if origin_path.exists():
                    metadata = json.loads(origin_path.read_text())
                    stamp = metadata.get('operation_started_ns')
                    if type(stamp) is int and stamp > 0:
                        self.origin_ns = stamp
                candidate = self.last_before_origin
                if (self.origin_ns is not None and candidate is not None
                        and candidate.get('observed_ns') is not None
                        and candidate['observed_ns'] <= self.origin_ns
                        and candidate.get('instructions') is not None):
                    self.baseline = candidate
            if type(cpu) not in (int, float) or not math.isfinite(cpu) or cpu < 0:
                self.write('search_CPU_unavailable')
                return
            active_search = sample.get('search_active')
            if type(active_search) is not bool:
                self.write('search_active_unavailable')
                return
            self.max_search_cpu = max(cpu, self.max_search_cpu or 0)
            while self.next_threshold <= cpu:
                baseline_count = self.baseline['instructions'] if self.baseline else None
                count = snapshot['instructions']
                threshold = self.next_threshold
                self.rows.append(dict(
                    threshold_search_CPU_seconds=threshold,
                    observed_search_CPU_seconds=cpu,
                    threshold_overshoot_CPU_seconds=cpu - threshold,
                    observed_ns=now_ns, counter=snapshot, baseline=self.baseline,
                    instructions_since_observed_baseline=(count - baseline_count
                        if count is not None and baseline_count is not None else None),
                    baseline_failure=(None if baseline_count is not None
                                      else 'pre_origin_counter_baseline_unavailable'),
                    baseline_qualification='Last counter observation before the search origin; not exact search-only instructions.',
                    baseline_gap_ns=(self.origin_ns - self.baseline['observed_ns']
                                     if self.baseline else None),
                    origin_timestamp_ns=self.origin_ns,
                    search_active=active_search,
                    sample_phase=('active_search' if active_search else 'inactive_or_final'),
                    may_include_post_search_instructions=not active_search,
                    instruction_qualification=(
                        'Active search sample; full MCP-session inherited instructions.'
                        if active_search else
                        'Inactive or final sample; full MCP-session inherited instructions may include post-search work.'),
                    exact_threshold_sample=False,
                    scope='Full MCP-session inherited instructions at a search CPU crossing.'))
                self.next_threshold += INTERVAL_CPU_SECONDS
            if active_search is True and cpu >= LONG_SEARCH_CPU_SECONDS:
                self.directory.mkdir(parents=True, exist_ok=True)
                created = create_once(self.directory / 'LONG-SEARCH.json', dict(
                    case=self.case, threshold_search_CPU_seconds=LONG_SEARCH_CPU_SECONDS,
                    observed_search_CPU_seconds=cpu,
                    threshold_overshoot_CPU_seconds=cpu - LONG_SEARCH_CPU_SECONDS,
                    observed_ns=now_ns, search_active=True, counter=snapshot,
                    action='report_only', signals_sent=0, claims_added=0,
                    scope='Owned aggregate search CPU; no job stop.'))
                if not created:
                    previous = json.loads((self.directory / 'LONG-SEARCH.json').read_text())
                    if not isinstance(previous, dict) or previous.get('case') != self.case:
                        raise ValueError('The long-search marker belongs to another case.')
            self.write(failure)
        except (OSError, ValueError, TypeError, KeyError, OverflowError):
            try:
                self.write('checkpoint_observer_failed')
            except (OSError, ValueError, TypeError):
                pass

    def write(self, failure):
        self.directory.mkdir(parents=True, exist_ok=True)
        atomic(self.directory / 'CHECKPOINTS.json', dict(
            case=self.case, block=self.case['block'], event='instructions:u', interval_ms=1000,
            threshold_interval_search_CPU_seconds=INTERVAL_CPU_SECONDS,
            thresholds_search_CPU_seconds=[row['threshold_search_CPU_seconds'] for row in self.rows],
            checkpoints=self.rows, next_threshold_search_CPU_seconds=self.next_threshold,
            maximum_observed_search_CPU_seconds=self.max_search_cpu,
            failure=failure, polling_source='Existing guard memory/CPU loop',
            threshold_clock='Owned aggregate search CPU; not wall time',
            instruction_scope='MCP session and inherited descendants',
            exact_threshold_samples=False, new_processes=0, new_claims=0,
            raw_counter_path=str(self.counter.path), signals_sent=0))
