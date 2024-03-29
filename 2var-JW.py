import sys

# improve: split check_clause and divide to 2 places where used
# improve: use activities

#outcommented: activities(working), 2variableScheme(not working yet), clauseResulution(not working yet)
#before handin: satt() direct in hasState, DPLL, BCP etc. , unsatt() direkt in backtr ack. remove run_all. parse_dimacs ohne "file"

#hasState -> Richtige clauses erinnern, oder andere methode
#2varscheme
#jeroslow wang mit beiden var und minus var
#conflict res 

def parse_dimacs():
    clauses = []
    with open(sys.argv[1], 'r') as input_file:  # 
        for line in input_file:
            if line[0] in ['c', 'p']:
                continue
            literals = list(map(int, line.split()))
            assert literals[-1] == 0
            literals = literals[:-1]
            clauses.append(literals)
    clauses = [list(set(clause)) for clause in clauses if len(set(clause)) == len(set([abs(var) for var in clause]))]
    return clauses

def setup(clauses):
    variable_set = set()
    for clause in clauses:
        variable_set = variable_set.union(clause)
    variable_set_both = variable_set
    variable_set_abs = [abs(ele) for ele in variable_set]
    variable_set_abs = list(set(variable_set_abs))
    num_vars_abs = len(variable_set_abs)
    trail = []
    watch = {}
    watched_variables = {}
    JW = {}
    for var_abs in variable_set_abs:
        JW[var_abs] = 0
        watch[var_abs] = []
        watch[-var_abs] = []
    for clause in clauses:
        JW_of_clause = 2**-len(clause)
        for var in clause:
            JW[abs(var)] += JW_of_clause
    clauses_sat = []
    dat={}
    dat["prop_schedule"] = []
    dat["clauses"] = clauses
    dat["watch"] = watch
    dat["trail"] = trail
    dat["JW"] = JW
    dat["clauses_satisfied"] = clauses_sat
    dat["watched_variables"] = watched_variables
    dat["num_vars_abs"] = num_vars_abs
    dat["variable_set_abs"] = variable_set_abs
    dat["variable_set_both"] = variable_set_both
    for clause_index, clause in enumerate(clauses):
        watched_variables[clause_index] = []
    return dat

def initial_assignments(dat):
    for clause_index in range(len(dat["clauses"])):
        clause_this = dat["clauses"][clause_index]
        dat["watch"][clause_this[0]].append(clause_index)
        dat["watched_variables"][clause_index].append(clause_this[0])
        var, state = find_next_var_to_watch(dat, clause_index, 0)
        if state != "resolved":                                 #improve hier checken/propaggaten
            dat["watch"][var].append(clause_index)
            dat["watched_variables"][clause_index].append(var)

def DPLL(clauses):
    dat = setup(clauses)
    initial_assignments(dat)
    decide(dat)

def propagate(dat, var_old):
    watch_this = dat["watch"][-var_old].copy()
    for clause_index in watch_this:
        var_new, state_new = find_next_var_to_watch(dat, clause_index, -var_old)
        if state_new == "unit":
            dat["trail"].append([var_new, clause_index])
            dat["prop_schedule"].append(var_new) # TODO biswohin backktrack , als liste?
        elif state_new == "unresolved":
            dat["watch"][var_new].append(clause_index)
            dat["watched_variables"][clause_index].append(var_new)
            dat["watch"][-var_old].remove(clause_index)     #wirklich -var?
            dat["watched_variables"][clause_index].remove(-var_old) 
        elif state_new == "resolved":
            state_resolved = check_clause(dat, clause_index)
            if state_resolved == "unsat":
                backtrack(dat, 0, clause_index)  # 0 hier ändern wenn activations.
    if len(dat["prop_schedule"]) == 0:
        decide(dat)
    else:
        var_new = dat["prop_schedule"][0]
        del dat["prop_schedule"][0]
        propagate(dat, var_new)
    
        
def find_next_var_to_watch(dat, clause_index, var_old_neg):
    clause_abs = [abs(ele) for ele in dat["clauses"][clause_index]]
    vars_assigned = get_assigned_variables(dat)
    vars_assigned_abs =  [abs(ele) for ele in vars_assigned]
    vars_watched = dat["watched_variables"][clause_index]
    vars_watched_abs =  [abs(ele) for ele in vars_watched]
    vars_open_abs = [x for x in clause_abs if x not in vars_watched_abs]
    vars_open_abs = [x for x in vars_open_abs if x not in vars_assigned_abs]
    vars_open_abs_len = len(vars_open_abs)
    if vars_open_abs_len == 0:
        if check_clause(dat, clause_index) == "sat":
            return False, "resolved"
        vars_watched_and_unassigned = [x for x in vars_watched if x not in vars_assigned and x not in [var_old_neg]]
        if len(vars_watched_and_unassigned) == 1: # unit
            return vars_watched_and_unassigned[0], "unit"
        elif len(vars_watched_and_unassigned) == 0: # sat or unsat?2
#            state_clause = check_cclause(dat, clause_index)
            return False, "resolved"
    else:
        var = vars_open_abs[0]
        if -var in dat["clauses"][clause_index]:
            var = -var
    return var, "unresolved"
        
def check_clause(dat, clause_index):
    assigned = get_assigned_variables(dat)
    unsatisfied_vars = 0
    for var in dat["clauses"][clause_index]:
        if -var in assigned:
            unsatisfied_vars = unsatisfied_vars+1
        elif var in assigned:
            return "sat"
    if unsatisfied_vars == len(dat["clauses"][clause_index]):
        return "unsat"

def check_formular(dat): # has to be fully assigned
    assigned = get_assigned_variables(dat)
    satisfied_clauses = 0
    for clause_index, clause in enumerate(dat["clauses"]):
        unsatisfied_vars = 0
        for var in dat["clauses"][clause_index]:
            if -var in assigned:
                unsatisfied_vars = unsatisfied_vars+1
            elif var in assigned:
                satisfied_clauses += 1
                break
        if unsatisfied_vars == len(dat["clauses"][clause_index]):
            backtrack(dat, var, clause_index)
    if satisfied_clauses == len(dat["clauses"]):
        sat()

def decide(dat):
    assigned = get_assigned_variables(dat)
    assigned_abs = [abs(x) for x in assigned]
    JW_unassigned = {key:value for key, value in dat["JW"].items() if key not in assigned_abs}
    if len(JW_unassigned) == 0:
        state = check_formular(dat)
        if state == "sat":
            sat()   #should not be possible to be unsat because for each clause checkk_clause does backktrack
        else: 
            print("ERROR SHOULD NOT HAPPEN")
    var = key_with_max_val(JW_unassigned)
    dat["trail"].append([var, "DL"]) # var, DL or clause # negative first or JW for both?
    propagate(dat, var)

def backtrack(dat, var, clause_index):
    conflict_parts = [[var, clause_index]]
    while True:
        if len(dat["trail"]) == 0:
            unsat()
        var, DL_or_cl = dat["trail"][-1]
        conflict_parts.append([var, DL_or_cl])
        del dat["trail"][-1]
        if DL_or_cl == "DL": break;
    del dat["prop_schedule"][:] # brauche nicht? ist ja nicht mehr assigned, also kann ruhig watch ändern. sollte keine units mehr geben?
    dat["trail"].append([-var, "backtrack"])
    propagate(dat, -var)

def key_with_max_val(JW_unassigned):
    v=list(JW_unassigned.values())
    k=list(JW_unassigned.keys())
    return k[v.index(max(v))]

def get_watched_variables(watch, clause_index):
    variables = [var for var, cl_index in enumerate(watch) if cl_index == clause_index]
    return variables

def get_assigned_variables(dat):
    assigned = []
    for trai in dat["trail"]:
        assigned.append(trai[0])
    return assigned

def unsat():
    print("unsat")
    sys.exit(20)

def sat():
    print("sat")
    sys.exit(10)

DPLL(parse_dimacs())

#def hasState(dat): # not necessary bec of two watched lit scheme?
#    sat_clauses_counter = 0
#    for cl_index, clause in enumerate(dat["clauses"]):
#        state_clause, var = check_clauase1(dat, cl_index, clause)
#        if state_clause == "unsat":
#            return "unsat", var, cl_index
#        if state_clause == "sat":
#            sat_clauses_counter = sat_clauses_counter+1
#        if state_clause == "unit":
#            return "unit", var, cl_index
#    if sat_clauses_counter == len(dat["clauses"]):
#        return "sat", 0, 0 # exit
#    return "unresolved", var, cl_index

#def manage_activity_counter(dat, conflict_parts):
#    increase_activities(dat, conflict_parts)
#    dat["activity_division_counter"] = dat["activity_division_counter"]-1
#    if dat["activity_division_counter"] == 0:
#        for var in dat["variable_set_abs"]:
#            dat["activities"][var] = dat["activities"][var]/2
#        dat["activity_division_counter"] = dat["activity_counter_setting"]
#
#def increase_activities(dat, conflict_parts):
#    for part in conflict_parts:
#        var = part[0]
#        if var < 0:var = var*-1
#        dat["activities"][var] = dat["activities"][var]+1

