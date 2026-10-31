"""Apply the released CPU exception only to authorized PORT natives."""
from memory_policy import PORT_KIND, production_port_case, read, validate_job

PERF = {'path': '/usr/bin/perf',
        'sha256': 'f48c2da1af219a48d5b959f4f874b3c6e64eab07211610c9435558898fe625dc'}

def port_case(memory_job):
    if not isinstance(memory_job, dict) or memory_job.get('phase') != 'native':
        return None
    workload = memory_job.get('workload') or {}
    if workload.get('kind') != PORT_KIND:
        return None
    validate_job(memory_job)
    _, case = production_port_case(read(workload['profile']), memory_job)
    return dict(case)

def cpu_budgets(memory_job, search_default=7200, setup_default=None):
    return (None, None) if port_case(memory_job) is not None else (search_default, setup_default)


def configure_cpu(runtime, memory_job):
    search_budget, setup_budget = cpu_budgets(memory_job)
    runtime['cache_attempt']['limits']['cpu_seconds'] = search_budget
    policy = dict(window_seconds=search_budget, setup_budget_seconds=setup_budget,
                  origin='exact_native_rocq_check_dispatch', prerequisites_excluded=True)
    if port_case(memory_job) is not None:
        policy.update(instruction_checkpoint_search_CPU_seconds=600,
                      long_search_report_CPU_seconds=21600, kill_on_long_search=False,
                      perf_executable=dict(PERF))
    runtime['search_CPU_policy'] = policy
    return search_budget, setup_budget
