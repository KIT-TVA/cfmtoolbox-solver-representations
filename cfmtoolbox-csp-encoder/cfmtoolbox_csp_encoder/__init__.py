from cfmtoolbox import app, CFM, Feature
from cfmtoolbox_ilp_encoder import get_max_interval_value
from ortools.sat.python import cp_model
from cfmtoolbox_csp_encoder.multisetCSP import (create_multiset_csp_encoding,create_const_name,
                                                get_variables)


@app.command()
def run_csp_solver_maximize_cardinalities(cfm: CFM):
    model = create_multiset_csp_encoding(cfm)

    variables = get_variables()
    try:
        model.Validate()
        print("Model is valid.")
    except Exception as e:
        print(f"Model validation failed: {e}")

    solver = cp_model.CpSolver()
    status = solver.solve(model)
    if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
        for key in variables:
           print(key + ": " + str(solver.Value(variables[key])))

    find_actual_max(model,cfm.root,1)



def find_actual_max(model, feature: Feature, max_parent_cardinality: int):
    variables = get_variables()


    model.maximize(variables[create_const_name(feature)])

    solver = cp_model.CpSolver()
    solver.parameters.log_search_progress = True
    solver.parameters.cp_model_probing_level = 0  # Enable presolve (default)
    #solver.parameters.num_search_workers = 1  # Single-threaded for deterministic debugging
    status = solver.solve(model)


    if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
        #print(solver.objective_value)
        if int(solver.objective_value) > 1:
            actual_max = int(solver.objective_value) / max_parent_cardinality
            new_max = round(max_parent_cardinality * actual_max, None)
        else:
            actual_max = int(solver.objective_value)
            new_max = max_parent_cardinality
        if actual_max < get_max_interval_value(feature.instance_cardinality.intervals):
            print(feature.name + ": ")
            print("Given feature instance cardinality: " + str(get_max_interval_value(
                feature.instance_cardinality.intervals)) + "\n")
            print("Actual Max Feature Instance Cardinality " + str(round(actual_max, None)) + "\n")
        for key in variables:
            print(key + ": " + str(solver.Value(variables[key])))
    else:
        print("No solution found.")
        new_max = 0


    '''
    print("\nStatistics")
    print(f"  status   : {solver.status_name(status)}")
    print(f"  conflicts: {solver.num_conflicts}")
    print(f"  branches : {solver.num_branches}")
    print(f"  wall time: {solver.wall_time} s")
    '''
    for child in feature.children:
        find_actual_max(model, child, new_max)


    #        for variable in solver.variables():
       #     print(f"{variable.name()} = {variable.solution_value()}")