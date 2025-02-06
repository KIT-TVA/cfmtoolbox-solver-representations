from cfmtoolbox import CFM, Feature, Constraint, Interval
from cfmtoolbox.plugins.big_m import get_global_upper_bound
from ortools.sat.python import cp_model
from ortools.sat.python.cp_model import CpModel

big_m = 0
variables = {}

def create_multiset_csp_encoding(cfm: CFM):
    global big_m
    big_m = get_global_upper_bound(cfm.root)
    #print(big_m)
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
        variables[create_const_name_activ(feature)] = model.new_bool_var(create_const_name_activ(feature))
        variables[create_const_name_activ_global(feature)] = model.new_bool_var(create_const_name_activ_global(feature))

        # if a feature has >= 1 instances it is considered global activ
        model.add(
            variables[create_const_name(feature)] > 0).only_enforce_if(
            variables[create_const_name_activ_global(feature)]
        )
        model.add(variables[create_const_name(feature)] == 0).only_enforce_if(
            variables[create_const_name_activ_global(feature)].Not())

        # if a feature is local active it is also global active
        model.add_implication(variables[create_const_name_activ(feature)], variables[
          create_const_name_activ_global(feature)])
        #print(create_const_name_activ(feature)+ "->" + create_const_name_activ_global(feature))



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
            """
            print(feature_variable.name + ">=" + str(
                feature.instance_cardinality.intervals.__getitem__(0).lower) + " * " +
                  parent_variable.name)
            print(feature_variable.name + "<=" + str(
                feature.instance_cardinality.intervals.__getitem__(0).upper) + " * " +
                  parent_variable.name)
            """
            model.add(feature_variable >=
                      feature.instance_cardinality.intervals.__getitem__(0).lower * parent_variable)
            model.add(feature_variable <=
                      feature.instance_cardinality.intervals.__getitem__(0).upper * parent_variable)
        else:
            model.add(feature_variable >= feature.instance_cardinality.intervals.__getitem__(
                0).lower)
            """
            print(feature_variable.name + ">=" + str(
                feature.instance_cardinality.intervals.__getitem__(0).lower))
            print(feature_variable.name + "<=" + str(
                feature.instance_cardinality.intervals.__getitem__(0).upper))
            """
            model.add(feature_variable <= feature.instance_cardinality.intervals.__getitem__(
                0).upper)


    for child in feature.children:
        create_assert_feature_instance_cardinality(child, model)


def create_assert_group_instance_cardinality(feature: Feature, model: CpModel):
    max_upperbound = get_max_interval_value(feature.group_instance_cardinality.intervals)
    min_lowerbound = get_min_interval_value(feature.group_instance_cardinality.intervals)


    sum_variables = []

    if len(feature.children) > 0:
        for child in feature.children:
            sum_variables.append(variables[create_const_name(child)])

        upper_bound = big_m * len(feature.children)

        total_sum_variables = model.new_int_var(0, upper_bound, "total_sum_variables_" + str(
            feature.name))
        model.add(total_sum_variables == sum(sum_variables)).only_enforce_if(variables[
                                                                                 create_const_name_activ_global(feature)])
       # print(total_sum_variables.name + "="  + sum(sum_variables).__str__())

        parent_variable = variables[create_const_name(feature)]
        model.add(total_sum_variables >= min_lowerbound * parent_variable)
        model.add(total_sum_variables <= max_upperbound * parent_variable)
        """
        print(sum(sum_variables).__str__() + ">="  + str(
            feature.group_instance_cardinality.intervals.__getitem__(0).lower) + " * " + parent_variable.name)
        print(sum(sum_variables).__str__() + "<=" + str(
            feature.group_instance_cardinality.intervals.__getitem__(
                0).upper) + " * " + parent_variable.name)
        """
        for child in feature.children:
            create_assert_group_instance_cardinality(child, model)


def create_assert_group_type_cardinality(feature: Feature, model: CpModel):
    max_upperbound = get_max_interval_value(feature.group_type_cardinality.intervals)
    min_lowerbound = get_min_interval_value(feature.group_type_cardinality.intervals)

    if len(feature.children) > 0:
        global_active_parent = variables[create_const_name_activ_global(feature)]
        sum_type_variables = []
        for child in feature.children:
            local_active_variable = variables[create_const_name_activ(child)]

            x_ge_y = model.NewBoolVar(child.name  + '_ge_' + child.parent.name)  # Represents x
            # >= y

            # if child >= parent than the constant child_active should be true
            model.add(variables[create_const_name(child)] >= variables[create_const_name(
                child.parent)]).only_enforce_if(x_ge_y)

            # else if child < parent the constant child_active should be false
            model.add(variables[create_const_name(child)] < variables[create_const_name(
                child.parent)]).only_enforce_if(x_ge_y.Not())

            model.AddBoolAnd([x_ge_y, global_active_parent]).OnlyEnforceIf(local_active_variable)
            model.AddBoolOr([x_ge_y.Not(), global_active_parent.Not()]).OnlyEnforceIf(local_active_variable.Not())




            sum_type_variables.append(local_active_variable)

        type_sum_variables = model.new_int_var(0, len(sum_type_variables), "type_sum_variables" + str(
            feature.name))
        model.add(type_sum_variables == sum(sum_type_variables)).only_enforce_if(global_active_parent)

        model.add(type_sum_variables >= min_lowerbound).only_enforce_if(global_active_parent)
        model.add(type_sum_variables <= max_upperbound).only_enforce_if(global_active_parent)
        """
        print(sum(sum_type_variables).__str__() + ">=" + str(
            feature.group_type_cardinality.intervals.__getitem__(
                0).lower) + " * " + global_active_parent.name)
        print(sum(sum_type_variables).__str__() + "<=" + str(
            feature.group_type_cardinality.intervals.__getitem__(
                0).upper) + " * " + global_active_parent.name)
        """
        for child in feature.children:
            create_assert_group_type_cardinality(child, model)



def create_assert_for_constraints(constraints: list[Constraint], model: CpModel):

    for i,constraint in enumerate(constraints):
        first_interval_constant = model.new_bool_var("constraint_first_interval_literal_" +
                                                     str(i))
        first_interval = constraint.first_cardinality.intervals.__getitem__(0)

        variables["constraint_first_interval_literal_" +
                  str(i)] = first_interval_constant

        model.add(variables[create_const_name(constraint.first_feature)] >=
                  first_interval.lower).only_enforce_if(first_interval_constant)
        model.add(variables[create_const_name(constraint.first_feature)] <=
                  first_interval.upper).only_enforce_if(first_interval_constant)

        out_of_range_low = model.NewBoolVar('out_of_range_low')
        out_of_range_high = model.NewBoolVar('out_of_range_high')

        # Define the conditions for the OR
        model.Add(variables[create_const_name(constraint.first_feature)] < first_interval.lower).only_enforce_if(out_of_range_low)
        model.Add(variables[create_const_name(
            constraint.first_feature)] > first_interval.upper).only_enforce_if(out_of_range_high)

        model.AddBoolOr([out_of_range_low, out_of_range_high]).only_enforce_if(
            first_interval_constant.Not())

        second_interval_constant = model.new_bool_var("constraint_second_interval_literal_" +
                                                     str(i))
        variables["constraint_second_interval_literal_" +
                                                     str(i)] = second_interval_constant


        second_interval = constraint.second_cardinality.intervals.__getitem__(0)
        model.add(variables[create_const_name(constraint.second_feature)] >=
                  second_interval.lower).only_enforce_if(second_interval_constant)
        model.add(variables[create_const_name(constraint.second_feature)] <= second_interval.upper).only_enforce_if(second_interval_constant)

        out_of_range_low_2 = model.NewBoolVar('out_of_range_low')
        out_of_range_high_2 = model.NewBoolVar('out_of_range_high')

        model.Add(variables[create_const_name(
            constraint.second_feature)] < second_interval.lower).only_enforce_if(out_of_range_low_2)
        model.Add(variables[create_const_name(
            constraint.second_feature)] > second_interval.upper).only_enforce_if(out_of_range_high_2)

        model.AddBoolOr([out_of_range_low_2, out_of_range_high_2]).only_enforce_if(
            second_interval_constant.Not())

        if constraint.require:
            model.add_implication(first_interval_constant, second_interval_constant)
        else:
            model.add(first_interval_constant + second_interval_constant <= 1)



def get_max_interval_value(intervals: list[Interval])-> int:
    if len(intervals) == 0:
        return 0
    else:
        max_upperbound = intervals[0].upper
        for interval in intervals:
            if interval.upper > max_upperbound:
                max_upperbound = interval.upper
        return max_upperbound


def get_min_interval_value(intervals: list[Interval])-> int:
    if len(intervals) == 0:
        return 0
    else:
        min_lowerbound = intervals[0].lower
        for interval in intervals:
            if interval.lower < min_lowerbound:
                min_lowerbound = interval.lower
        return min_lowerbound


def create_const_name(feature: Feature) -> str:
    return "Feature_" + feature.name

def create_const_name_activ(feature: Feature) -> str:
    return create_const_name(feature) + "_activ"

def create_const_name_activ_global(feature: Feature) -> str:
    return create_const_name(feature) + "_activ_global"



