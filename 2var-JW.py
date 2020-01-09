import sys

#outcommented: activities(working), 2variableScheme(not working yet), clauseResulution(not working yet)
#before handin: sat() direct in hasState, DPLL, BCP etc. , unsat() direkt in backtrack. remove run_all. parse_dimacs ohne "file"

#hasState -> Richtige clauses erinnern, oder andere methode
#2varscheme
#jeroslow wang mit beiden var und minus var
#conflict res 

def run_all(von, bis):
    for i in range(von, bis):
        start_this = datetime.datetime.now()
        run("cnf/example-"+str(i)+".cnf")
        finish_this = datetime.datetime.now()
        print("file = "+ str(i)+", exec time = "+str(finish_this-start_this))

def run(file):
    result = DPLL(parse_dimacs(file))
    if result == "unsat":unsat()
    else:sat()

def parse_dimacs(file):
    clauses = []
    with open(file, 'r') as input_file:  # sys.argv[1]
        for line in input_file:
            if line[0] in ['c', 'p']:
                continue
            literals = list(map(int, line.split()))
            assert literals[-1] == 0
            literals = literals[:-1]
            clauses.append(literals)
    start_delete = datetime.datetime.now()
    clauses = [list(set(clause)) for clause in clauses if len(set(clause)) == len(set([abs(var) for var in clause]))]
    finish_delete = datetime.datetime.now()
    print("delete time = "+str(finish_delete-start_delete))
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
    for var_both in variable_set_both:
        watch[var_both] = []
    for clause in clauses:
        JW_of_clause = 2**-len(clause)
        for var in clause:
            JW[abs(var)] += JW_of_clause
    clauses_sat = []
    dat={}
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

def DPLL(clauses):
    dat = setup(clauses)
    for clause_index in range(len(clauses)):
        for i in [0,1]:
            var, state = find_next_var_to_watch(dat, clause_index)
            print(state)
            if state != "resolved":
                dat["trail"].append([var, clause_index])
                propagate(dat, clause_index, False)
    print("before first decide")
    decide(dat)

def propagate(dat, clause_index, var):
    print(dat["watch"])
    watch_this = dat["watch"][var].copy()
    for clause_index in watch_this:
        added, var_added = add_and_remove_watch(dat, clause_index, var)
        
def find_next_var_to_watch(dat, clause_index):
    clause_abs = [abs(ele) for ele in dat["clauses"][clause_index]]
    vars_assigned = get_assigned_variables(dat)
    vars_assigned_abs =  [abs(ele) for ele in vars_assigned]
    vars_watched = dat["watched_variables"][clause_index]
    vars_watched_abs =  [abs(ele) for ele in vars_watched]
    vars_open_abs = [x for x in clause_abs if x not in vars_watched_abs]
    vars_open_abs = [x for x in vars_open_abs if x not in vars_assigned_abs]
    vars_open_abs_len = len(vars_open_abs)
    if vars_open_abs_len == 0:
        vars_watched_and_unassigned = [x for x in vars_watched if x not in vars_assigned]
        if len(vars_watched_and_unassigned) == 1: # unit
            return vars_watched_and_unassigned[0], "unit"
        elif len(vars_watched_and_unassigned) == 0: # sat or unsat?
            return False, "resolved"
    else:
        var = vars_open_abs[0]
        if -var in dat["clauses"][clause_index]:
            var = -var
    return var, "unresolved"

def add_and_remove_watch(dat, clause_index, var_old):
    var_new, state = find_next_var_to_watch(dat, clause_index)
    if state == "unit":
        dat["trail"].append([var_new, clause_index])
        propagate(dat, clause_index, var_new)
        return
    if state == "resolved":
        check_clause(dat, clause_index)
        return 
    if state == "unresolved":
        dat["watch"][var_new].append(clause_index)
        dat["watched_variables"][clause_index].append(var_new)
        dat["watch"][var_old].remove(clause_index)
        dat["watched_variables"][clause_index].remove(var_old)      # eigentlich anstatt von hasStatte an dieser stelle nach unit checken.dann wird erst 2varscheme benutzt. propaate bevor alle watches gelöscht sind. watch nur löschen wenn woanders geadded wurde

def check_clause(dat, clause_index):
    assigned = get_assigned_variables(dat)
    unsatisfied_vars = 0
    for var in dat["clauses"][clause_index]:
        if -var in assigned:
            unsatisfied_vars = unsatisfied_vars+1
        elif var in assigned:
            return
    if unsatisfied_vars == len(dat["clauses"][clause_index]):
        backtrack()

def decide(dat):
    assigned = get_assigned_variables(dat)
    assigned_abs = [abs(x) for x in assigned]
    JW_unassigned = {key:value for key, value in dat["JW"].items() if key not in assigned_abs}
    if len(JW_unassigned) == 0:
        sat()
    var = keywithmaxval(JW_unassigned)
    dat["trail"].append([var, "DL"]) # var, DL or clause # negative first or JW for both?
    propagate(dat, var)

def backtrack(dat, var, cl_index):
    conflict_parts = [[var, cl_index]]
    while True:
        if len(dat["trail"]) == 0:
            unsat()
        var, DL_or_cl = dat["trail"][-1]
        conflict_parts.append([var, DL_or_cl])
        del dat["trail"][-1]
        if DL_or_cl == "DL": break;
    dat["trail"].append([-var, "Backtrack"])

def keywithmaxval(JW_unassigned):
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

import datetime
start = datetime.datetime.now()
run_all(0,1) # problem: 41 . loop
finish = datetime.datetime.now()
print(finish-start)


#def hasState(dat): # not necessary bec of two watched lit scheme?
#    sat_clauses_counter = 0
#    for cl_index, clause in enumerate(dat["clauses"]):
#        state_clause, var = check_clause(dat, cl_index, clause)
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

