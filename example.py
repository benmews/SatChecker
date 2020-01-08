import sys

#outcommented: activities(working), 2variableScheme(not working yet), clauseResulution(not working yet)
#before handin: sat() direct in hasState, DPLL, BCP etc. , unsat() direkt in backtrack. remove run_all. parse_dimacs ohne "file"

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
            clauses = [list(set(clause)) for clause in clauses if len(set(clause)) == len(set([abs(var) for var in clause]))]

    return clauses

def setup(clauses):
    variable_set = []
    for clause in clauses:
        variable_set.extend(clause)
        variable_set = [abs(ele) for ele in variable_set]
        variable_set = list(set(variable_set))

    num_vars = len(variable_set)
    trail = []
#    activities = {}
    watch = {}
    watched_variables = {}

#    activity_counter_setting = 10
#    activity_division_counter = activity_counter_setting

    JW = {}
    for var in variable_set:
        JW[var] = 0
#        activities[var] = 0
        watch[var] = []
        watch[-var] = []

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
#    dat["activities"] = activities
    dat["watched_variables"] = watched_variables
    dat["num_vars"] = num_vars
    dat["variable_set"] = variable_set
#    dat["activity_division_counter"] = activity_division_counter
#    dat["activity_counter_setting"] = activity_counter_setting
    for clause_index, clause in enumerate(clauses):
        watched_variables[clause_index] = []
        for var in clause[0:2]:
            added, var = addToWatch(clause_index, clause, dat) # wenn 2scheme, auch hier prop
    return dat

#def manage_activity_counter(dat, conflict_parts):
#    increase_activities(dat, conflict_parts)
#    dat["activity_division_counter"] = dat["activity_division_counter"]-1
#    if dat["activity_division_counter"] == 0:
#        for var in dat["variable_set"]:
#            dat["activities"][var] = dat["activities"][var]/2
#        dat["activity_division_counter"] = dat["activity_counter_setting"]
#
#def increase_activities(dat, conflict_parts):
#    for part in conflict_parts:
#        var = part[0]
#        if var < 0:var = var*-1
#        dat["activities"][var] = dat["activities"][var]+1

def addToWatch(clause_index, clause, dat):
    clause_abs = [abs(ele) for ele in clause]
    vars_assigned = getAssignedVars(dat)
    vars_assigned_abs =  [abs(ele) for ele in vars_assigned]
    vars_watched = dat["watched_variables"][clause_index]
    vars_watched_abs =  [abs(ele) for ele in vars_watched]
    vars_open_abs = [x for x in clause_abs if x not in vars_watched_abs]
    vars_open_abs = [x for x in vars_open_abs if x not in vars_assigned_abs]
    vars_open_abs_len = len(vars_open_abs)
    var = vars_open_abs[0]
    var_abs = vars_open_abs[0]
    if var*-1 in clause:
        var = var*-1
    if vars_open_abs_len >= 1:
        dat["watch"][var].append(clause_index)
        dat["watched_variables"][clause_index].append(var)
        return "open", var_abs
    else:
        vars_watched_and_unassigned = [x for x in vars_watched if x not in vars_assigned]
        if len(vars_watched_and_unassigned) == 1:
            return "unit", var_abs
        if len(vars_watched_and_unassigned) == 0:
            return checkClause(dat, clause_index, clause)
        else:
            print("ERROR")
            sys.exit(1)

def addAndRemoveWatch(dat, var):
    watch_this = dat["watch"][var].copy()
    for clause_index in watch_this:
        added, var = addToWatch(clause_index, dat["clauses"][clause_index], dat)
        if added == "open":
            dat["watch"][var].remove(clause_index)
            dat["watched_variables"][clause_index].remove(var)      # eigentlich anstatt von hasStatte an dieser stelle nach unit checken.dann wird erst 2varscheme benutzt. propagate bevor alle watches gelöscht sind. watch nur löschen wenn woanders geadded wurde

    return added, var

def getWatchedVars(watch, clause_index):
    variables = [var for var, cl_index in enumerate(watch) if cl_index == clause_index]
    return variables

def getAssignedVars(dat):
    assigned = []
    for trai in dat["trail"]:
        assigned.append(trai[0])
    return assigned

def hasState(dat): # not necessary bec of two watched lit scheme?
    sat_clauses_counter = 0
    for cl_index, clause in enumerate(dat["clauses"]):
        state_clause, var = checkClause(dat, cl_index, clause)
        if state_clause == "unsat":
            return "unsat", var, cl_index
        if state_clause == "sat":
            sat_clauses_counter = sat_clauses_counter+1
        if state_clause == "unit":
            return "unit", var, cl_index
    if sat_clauses_counter == len(dat["clauses"]):
        return "sat", 0, 0 # exit
    return "unresolved", var, cl_index

def checkClause(dat, cl_index, clause):
    assigned = getAssignedVars(dat)
    unsatisfied_vars = 0
    openvars = []
    for var in clause:
        if var*-1 in assigned:
            unsatisfied_vars = unsatisfied_vars+1
        elif var in assigned:
            return "sat", var
        else:
            openvars.append(var)
    if unsatisfied_vars == len(clause):
        return "unsat", clause[0]
    lenopenvars = len(openvars)
    if lenopenvars == 1:
        return "unit", openvars[0]
    if lenopenvars >= 2:
        return "unresolved", openvars[0]

#def add_conflict_clause(dat, conflict_parts):
#    for part in conflict_parts[:-1]:
#        print(dat["clauses"][part[1]])
#    conflict_clause = dat["clauses"][conflict_parts[0][1]].copy()
#    for part in conflict_parts[1:-1]: # 0 is conflict variable, 1 is clause_index
#        other_clause = dat["clauses"][part[1]].copy()
#        if part[0] in conflict_clause:
#            conflict_clause.remove(part[0])
#            other_clause.remove(part[0]*-1)
#        else:
#            conflict_clause.remove(part[0]*-1)
#            other_clause.remove(part[0])
#        conflict_clause=list(set(conflict_clause+other_clause))
#    dat["clauses"].append(conflict_clause)

#    clause_index = len(dat["clauses"])
#    added, var = addToWatch(clause_index, conflict_clause, dat) # wenn 2scheme, auch hier prop
#    added, var = addToWatch(clause_index, conflict_clause, dat)

def decide(dat):
    assigned = getAssignedVars(dat)
    assigned_abs = [abs(x) for x in assigned]
#    unassigned_abs = [var for var in dat["variable_set"] if var not in assigned_abs]
#    activities_unassigned = {key:value for key, value in dat["activities"].items() if key in unassigned_abs}
#    var = max(activities_unassigned)
    JW_unassigned = {key:value for key, value in dat["JW"].items() if key not in assigned_abs}
    var = max(JW_unassigned)
    dat["trail"].append([var*-1, "DL"]) # var, DL or clause # negative first
#    added, var = addAndRemoveWatch(dat, var*-1)

def backtrack(dat, var, cl_index):
    conflict_parts = [[var, cl_index]]
    while True:
        if len(dat["trail"]) == 0:
            return "unsat"
        var, DL_or_cl = dat["trail"][-1]
        conflict_parts.append([var, DL_or_cl])
        del dat["trail"][-1]
        if DL_or_cl == "DL": break;
    dat["trail"].append([var*-1, "Backtrack"])
#    add_conflict_clause(dat, conflict_parts)
#    manage_activity_counter(dat, conflict_parts)
    return "goon"

def BCP(dat):
    while True:
        state, var, cl_index = hasState(dat)
        if state == "unsat":
            return state, var, cl_index
        elif state == "sat":
            return "sat", var, cl_index #exit
        elif state == "unit":
            dat["trail"].append([var, cl_index])
#            added, var = addAndRemoveWatch(dat, var*-1)
        elif state == "unresolved":
            return state, var, cl_index

def DPLL(clauses):
    dat = setup(clauses)
    while True:
        while True:
            BCP_result, var, cl_index = BCP(dat)
            if BCP_result == "unsat":
                backtrack_result = backtrack(dat, var, cl_index)
                if backtrack_result == "unsat":
                    return "unsat"
            if BCP_result == "sat":
                return "sat"
            if BCP_result == "unresolved": break
        decide(dat)

def run(file):
    result = DPLL(parse_dimacs(file))
    if result == "unsat":unsat()
    else:sat()

def unsat():
    print("unsat")
#    sys.exit(20)

def sat():
    print("sat")
#    sys.exit(10)

def run_all(von, bis):
    for i in range(von, bis):
        start_this = datetime.datetime.now()
        run("example-"+str(i)+".cnf")
        finish_this = datetime.datetime.now()
        print("file = "+ str(i)+", exec time = "+str(finish_this-start_this))

#test act vs jeroslow wang
#2watch

import datetime
start = datetime.datetime.now()
run_all(80,81)
finish = datetime.datetime.now()
print(finish-start)