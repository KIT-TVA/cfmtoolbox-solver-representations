from cfmtoolbox import CFM, Feature, Constraint
from cfmtoolbox.plugins.big_m import get_global_upper_bound
from ortools.sat.python import cp_model
from ortools.sat.python.cp_model import CpModel

big_m = 0
variables = {}

def create_multiset_csp_encoding(cfm: CFM):
    global big_m
    big_m = get_global_upper_bound(cfm.root)
    model = cp_model.CpModel()


    create_csp_variables(cfm, model)

    create_assert_feature_instance_cardinality(cfm.root,model)

    create_assert_group_instance_cardinality(cfm.root,model)

    create_assert_group_type_cardinality(cfm.root,model)

    create_assert_for_constraints(cfm.constraints,model)

    return model



def get_variables():
    global variables
    return variables

def create_csp_variables(cfm: CFM, model: CpModel):
    for feature in cfm.features:
        variables[create_const_name(feature)] = model.new_int_var(0, big_m, create_const_name(
            feature))




def create_assert_feature_instance_cardinality(feature: Feature, model: CpModel):

    feature_variable = variables[create_const_name(feature)]

    if feature.parent is not None:
        parent_variable = variables[create_const_name(feature.parent)]

    if len(feature.instance_cardinality.intervals) > 1:

        interval_literals = []

        for i,interval in enumerate(feature.instance_cardinality.intervals):
            interval_literal = model.new_bool_var("interval_literal_" + str(i) + "_" + feature.name)
            interval_literals.append(interval_literal)
            if feature.parent is not None:
                model.add(feature_variable >=
                          interval.lower * parent_variable).only_enforce_if(interval_literal)
                model.add(
                    feature_variable  <= interval.upper * parent_variable).only_enforce_if(interval_literal)
            else:
                model.add(
                    feature_variable >= interval.lower).only_enforce_if(interval_literal)
                model.add(
                    feature_variable <= interval.upper).only_enforce_if(interval_literal)

        model.add_bool_xor(interval_literals)

    else:

        if feature.parent is not None:
            print(feature_variable.name + ">=" + str(
                feature.instance_cardinality.intervals.__getitem__(0).lower) + " * " +
                  parent_variable.name)
            print(feature_variable.name + "<=" + str(
                feature.instance_cardinality.intervals.__getitem__(0).upper) + " * " +
                  parent_variable.name)
            model.add(feature_variable >=
                      feature.instance_cardinality.intervals.__getitem__(0).lower * parent_variable)
            model.add(feature_variable <=
                      feature.instance_cardinality.intervals.__getitem__(0).upper * parent_variable)
        else:
            model.add(feature_variable >= feature.instance_cardinality.intervals.__getitem__(
                0).lower)
            print(feature_variable.name + ">=" + str(
                feature.instance_cardinality.intervals.__getitem__(0).lower))
            print(feature_variable.name + "<=" + str(
                feature.instance_cardinality.intervals.__getitem__(0).upper))
            model.add(feature_variable <= feature.instance_cardinality.intervals.__getitem__(
                0).upper)


    for child in feature.children:
        create_assert_feature_instance_cardinality(child, model)


def create_assert_group_instance_cardinality(feature: Feature, model: CpModel):

    sum_variables = []

    if len(feature.children) > 0:

        for child in feature.children:
            sum_variables.append(variables[create_const_name(child)])

        total_sum_variables = model.new_int_var(0, big_m, "total_sum_variables_" + str(
            feature.name))
        model.add(total_sum_variables == sum(sum_variables))
        print(total_sum_variables.name + "="  + sum(sum_variables).__str__())

        parent_variable = variables[create_const_name(feature)]
        model.add(total_sum_variables >= feature.group_instance_cardinality.intervals.__getitem__(
        0).lower * parent_variable)
        model.add(total_sum_variables <= feature.group_instance_cardinality.intervals.__getitem__(
            0).upper * parent_variable)

        print(sum(sum_variables).__str__() + ">="  + str(
            feature.group_instance_cardinality.intervals.__getitem__(0).lower) + " * " + parent_variable.name)
        print(sum(sum_variables).__str__() + "<=" + str(
            feature.group_instance_cardinality.intervals.__getitem__(
                0).upper) + " * " + parent_variable.name)

        for child in feature.children:
            create_assert_group_instance_cardinality(child, model)


def create_assert_group_type_cardinality(feature: Feature, model: CpModel):

    sum_variables = []

    global_active_parent = model.new_bool_var("global_active_parent" + "_" + feature.name)
    model.add(
        variables[create_const_name(feature)] >= 1).only_enforce_if(
        global_active_parent)
    model.add(variables[create_const_name(feature)] < 1).only_enforce_if(global_active_parent.Not())

    if feature.parent is None:
        model.add(global_active_parent == 1)

    if len(feature.children) > 0:

        for child in feature.children:
            local_active_variable = model.new_bool_var("local_active_variable_" + str(child))
            model.add(variables[create_const_name(child)] >= variables[create_const_name(
                feature)]).only_enforce_if(local_active_variable)
            model.add(variables[create_const_name(child)] < variables[create_const_name(
                feature)]).only_enforce_if(local_active_variable.Not())
            sum_variables.append(local_active_variable)

        type_sum_variables = model.new_int_var(0, len(sum_variables), "type_sum_variables" + str(
            feature.name))
        model.add(type_sum_variables == sum(sum_variables))

        model.add(type_sum_variables >= feature.group_type_cardinality.intervals.__getitem__(
            0).lower).only_enforce_if(global_active_parent)
        model.add(type_sum_variables <= feature.group_type_cardinality.intervals.__getitem__(
            0).upper).only_enforce_if(global_active_parent)

        print(sum(sum_variables).__str__() + ">=" + str(
            feature.group_type_cardinality.intervals.__getitem__(
                0).lower) + " * " + global_active_parent.name)
        print(sum(sum_variables).__str__() + "<=" + str(
            feature.group_type_cardinality.intervals.__getitem__(
                0).upper) + " * " + global_active_parent.name)

        for child in feature.children:
            create_assert_group_type_cardinality(child, model)



def create_assert_for_constraints(constraints: list[Constraint], model: CpModel):

    for i,constraint in enumerate(constraints):
        first_interval_constant = model.new_bool_var("constraint_first_interval_literal_" +
                                                     str(i))
        first_interval = constraint.first_cardinality.intervals.__getitem__(0)
        model.add(variables[create_const_name(constraint.first_feature)] >=
                  first_interval.lower).only_enforce_if(first_interval_constant)
        model.add(variables[create_const_name(constraint.first_feature)] <= first_interval.upper).only_enforce_if(first_interval_constant)

        second_interval_constant = model.new_bool_var("constraint_second_interval_literal_" +
                                                     str(i))
        second_interval = constraint.second_cardinality.intervals.__getitem__(0)
        model.add(variables[create_const_name(constraint.second_feature)] >=
                  second_interval.lower).only_enforce_if(second_interval_constant)
        model.add(variables[create_const_name(constraint.second_feature)] <= second_interval.upper).only_enforce_if(second_interval_constant)

        if constraint.require:
            model.add_implication(first_interval_constant, second_interval_constant)
        else:
            model.add(first_interval_constant + second_interval_constant <= 1)







def create_const_name(feature: Feature) -> str:
    return "Feature_" + feature.name



