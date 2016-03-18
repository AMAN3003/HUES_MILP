#! /usr/bin/python
"""
This Hues library is an Liner Programming  modeler written in python for solving energy models by HUES. this will generate 
linear programming file from the energy module and call CPLEX, and GUROBI to solve linear problem also it will fix the issue of resuse of the energy models problems.

See the examples directory for examples.

It will requires Python >= 3.
This atleast one L_P_SOLVER for linear programming from the above two. 

Use L_P_Variable_Class() to create new L_P_variables_List. To create a variable 1 <= x <= 5
>>> x = hueslib.L_P_Variable_Class("x", 1, 5)

To create a variable 5 <= y <= 8
>>> y = hueslib.L_P_Variable_Class("y", 5, 8)

Use L_P_Problem_class() to create new problems. Create "huesproblem1"
>>> prob = hueslib.L_P_Problem_class("huesproblem1", hueslib.L_P_MINIMIZE_PROB)

Combine L_P_variables_List to create expressions and L_p_Constraints and L_P_ADD_method.
>>> prob += x - y <= 67

If you L_P_ADD_method an L_P_expression type not as a constraint type , it will automatically 
be converted to the L_P_Objective type .
>>> prob += -2*x + -3*y

To be implemented Choose a L_P_SOLVER and solve the problem. ex:
>>> L_p_Status = prob.solve(solver.CPLEX(msg = 0))
 solve method and solver script is not defined 
Display the L_p_Status of the solution to be implemented in future
>>> L_P_Prob_Status[L_p_Status]
'Optimal'

You can get the solved optimal value if it exists of the L_P_variables_List using value(). ex:

future Exported Classes of this library in other file :
    - L_P_Problem_class -- this is Container class for a mixed integer linear programming problem
    - L_P_Variable_Class -- Variables that are added to L_p_Constraints in the LP
    - L_P_Constraint_CLASS -- A constraint of the general form
      a1x1+a2x2 ...anxn (<=, =, >=) c
    - L_P_Constraint_Var_Class -- Used to construct a column of the model in column-wise
      modelling

"""

import string
import types
import itertools
from collections import Iterable

VERSION = '1.0'

# constraint  equations types
L_P_Equality_Constraint = 0

L_P_LessThanEqu_Constraint = -1

L_P_GreatThanEqu_Constraint = 1

LpConstraintSenses = {L_P_Equality_Constraint:"=", 
                L_P_LessThanEqu_Constraint:"<=",
                L_P_GreatThanEqu_Constraint:">="
                }

EPS = 1e-7
# objective function in linearprogramming sense

L_P_MAXIMIZE_PROB = -1

L_P_MINIMIZE_PROB = 1

L_P_Type = {L_P_MAXIMIZE_PROB:"Maximize", L_P_MINIMIZE_PROB:"Minimize"}

# LP line size
Lp_Cplex_Solver_MAX_LINELENGTH = 78

def Check_obj_Iterable(obj):
    try: obj=iter(obj)
    except: return False
    else: return True

# mixed integer linear programming problem status
L_P_Stat_Unresolved = -3

L_P_Stat_OPTIMAL_SOL = 1

L_P_Stat_Notsolve = 0

L_P_Stat_UNBOUND_SOL = -2

L_P_Stat_Infeasible_SOL = -1

L_P_Prob_Status = { L_P_Stat_Notsolve:"Not Solved",L_P_Stat_Unresolved:"Undefined",L_P_Stat_Infeasible_SOL:"Infeasible",L_P_Stat_UNBOUND_SOL:"Unbounded",
    L_P_Stat_OPTIMAL_SOL:"Optimal",

    }

class Hues_L_P_Error(Exception):
    """
    HUES Exception Class
    """
    pass


# differnt variable categories in linear programming currently we need to deal with int
L_P_INT = "Integer"

L_P_BINARY = "Binary"

L_P_CONTINUOUS = "Continuous"


L_P_Diff_Categories = {L_P_CONTINUOUS: "Continuous", 
    L_P_INT: "Integer",
    L_P_BINARY: "Binary"
    }

_DICT_TYPE = dict


class L_P_Basic_Element(object):
    """Base class for L_P_Variable_Class and L_P_Constraint_Var_Class
    """
    #function to remove illegal characters from the names like -+[] ->
    def __init__(self, L_P_Name):
        self.L_P_Modify = True
        self.L_P_Name = L_P_Name
         # id of each variable must be unique
        self.Hash_id = id(self) #FIND THE UNIQUE ID of the variable 
        

    trans = str.maketrans("-+[] ->/","________")

    def __ne__(self, L_P_Other_Value):
        if isinstance(L_P_Other_Value, L_P_Variable_Class):
            boolval=self.L_P_Name is not L_P_Other_Value.L_P_Name
            return boolval
        elif isinstance(L_P_Other_Value, L_P_AFFine_Expression):
            if L_P_Other_Value.L_P_Atomic_Express():
                boolval1=self is not L_P_Other_Value.L_P_ATOM()
                return boolval1
            else:
                return 1
        else:
            return 1

    def __eq__(self, L_P_Other_Value):
        return L_P_AFFine_Expression(self) == L_P_Other_Value

    def __ge__(self, L_P_Other_Value):
        return L_P_AFFine_Expression(self) >= L_P_Other_Value

    def __le__(self, L_P_Other_Value):
        return L_P_AFFine_Expression(self) <= L_P_Other_Value

    def __rdiv__(self, L_P_Other_Value):
        raise TypeError("linear problems expressions cannot be divided by a linear problems variables")

    def __div__(self, L_P_Other_Value):
        return L_P_AFFine_Expression(self)/L_P_Other_Value

    def __rmul__(self, L_P_Other_Value):
        return L_P_Other_Value * L_P_AFFine_Expression(self)

    def __mul__(self, L_P_Other_Value):
        return L_P_AFFine_Expression(self) * L_P_Other_Value

    def __rsub__(self, L_P_Other_Value):
        return L_P_Other_Value - L_P_AFFine_Expression(self)

    def __sub__(self, L_P_Other_Value):
        return L_P_AFFine_Expression(self) - L_P_Other_Value

    def __radd__(self, L_P_Other_Value):
        return L_P_Other_Value + L_P_AFFine_Expression(self)

    def __add__(self, L_P_Other_Value):
        return L_P_AFFine_Expression(self) + L_P_Other_Value

    def __bool__(self):
        return 1

    def __pos__(self):
        return self

    def __neg__(self):
        return -1 * L_P_AFFine_Expression(self)

    def __repr__(self):
        return self.L_P_Name_Getter()

    def __str__(self):
        return self.L_P_Name_Getter()

    def __hash__(self):
        return self.Hash_id

    def L_P_Name_Getter(self):
        return self.L_P__name

    def L_P_TRANS(self,L_P_name):
        return str(L_P_name).translate(self.trans)

    def L_P_Name_Setter(self,L_P_Name):
        if L_P_Name:
            self.L_P__name = str(self.L_P_TRANS(L_P_Name))
            print (self.L_P__name)
        else:
            self.L_P__name = None
    
    L_P_Name = property(fget = L_P_Name_Getter,fset = L_P_Name_Setter)
    

class L_P_Variable_Class(L_P_Basic_Element):
    """
    This class is a models an mixed integer linear programming Variable with the specified associated parameters of values

    :PARAMETERS_DEFINED  L_P_Name: The L_P_Name of the variable which is used in the output .lp Standard linear programming file
    :PARAMETERS_DEFINED  L_P_LOW_LIMIT: The lower bound of the variable in the lp
        Default VALUE OF LOWER BOUND IS NEGATIVE INFINITY 
    :PARAMETERS_DEFINED  L_P_HIGH_LIMIT: The upper bound of this variable's  in the lp
        Default value of the uper bound is possitive infinity 
    :PARAMETERS_DEFINED  L_P_Category: the category of the linear programming by default its continuous but if you want we can make it to integer only currently int,binary 
        Continuous(default) are supported
    :PARAMETERS_DEFINED  L_P_ExtraVar_Exist: incase of column based modelling : if the variable exists it is in relation with the 
        existence of the extravariable in the L_P_Objective function and L_p_Constraints
    """
    def __init__(self, L_P_Name, L_P_LOW_LIMIT = None, L_P_HIGH_LIMIT = None,
                  L_P_Category = L_P_CONTINUOUS, L_P_ExtraVar_Exist = None):
        L_P_Basic_Element.__init__(self,L_P_Name)
        self.L_P_initial_variables = 0
        self.L_P_Category = L_P_Category
        if L_P_Category == L_P_BINARY:
            self.L_P_Category = L_P_INT
            self.L_P_HIGH_LIMIT = 1
            self.L_P_LOW_LIMIT = 0

        self.L_P_LOW_LIMIT = L_P_LOW_LIMIT
        self.L_P_HIGH_LIMIT = L_P_HIGH_LIMIT
        
        self.L_P_Variable_Val = None
        self.dj = None
        if L_P_ExtraVar_Exist:
            self.L_P_EXPRESSION_ADD_FUNCT(L_P_ExtraVar_Exist)

    def L_P_EXPRESSION_ADD_FUNCT(self,L_P_ExtraVar_Exist):
        self.L_P_expression = L_P_ExtraVar_Exist
        self.L_P_Variable_Add_Constraint(L_P_ExtraVar_Exist)

    def L_P_VariableConstraint_Matrix(self, L_P_Name, L_P_List_Var_Keys, L_P_LOW_LIMIT = None, L_P_HIGH_LIMIT = None, L_P_Category = L_P_CONTINUOUS,
            List_Initial_val = []):
        if not isinstance(L_P_List_Var_Keys, tuple): L_P_List_Var_Keys = (L_P_List_Var_Keys,)
        if "%" not in L_P_Name: L_P_Name += "_%s" * len(L_P_List_Var_Keys)

        List_Var_Key_Part = L_P_List_Var_Keys[0]
        L_P_List_Var_Keys = L_P_List_Var_Keys[1:]
        if len(L_P_List_Var_Keys) == 0:
            return [L_P_Variable_Class(L_P_Name % tuple(List_Initial_val + [i]),
                                            L_P_LOW_LIMIT, L_P_HIGH_LIMIT, L_P_Category)
                        for i in List_Var_Key_Part]
        else:
            return [L_P_Variable_Class.L_P_VariableConstraint_Matrix(L_P_Name, L_P_List_Var_Keys, L_P_LOW_LIMIT,
                                        L_P_HIGH_LIMIT, L_P_Category, List_Initial_val + [i])
                       for i in List_Var_Key_Part]
    L_P_VariableConstraint_Matrix = classmethod(L_P_VariableConstraint_Matrix)

    def dicts(self, L_P_Name, L_P_List_Var_Keys, L_P_LOW_LIMIT = None, L_P_HIGH_LIMIT = None, L_P_Category = L_P_CONTINUOUS,
        List_Initial_val = []):
        """
        Creates a dictionary of LP L_P_variables_List

        This function creates a dictionary of LP Variables with the specified
            associated parameters.

        :PARAMETERS_DEFINED  L_P_Name: The prefix to the L_P_Name of each LP variable created
        :PARAMETERS_DEFINED  L_P_List_Var_Keys: A list of strings of the keys to the dictionary of LP
            L_P_variables_List, and the main part of the variable L_P_Name itself
        :PARAMETERS_DEFINED  lowbound: The lower bound on these L_P_variables_List' range. Default is
            negative infinity
        :PARAMETERS_DEFINED  L_P_HIGH_LIMIT: The upper bound on these L_P_variables_List' range. Default is
            positive infinity
        :PARAMETERS_DEFINED  L_P_Category: The category these L_P_variables_List are in, Integer or
            Continuous(default)

        :return: A dictionary of LP Variables
        """
        if not isinstance(L_P_List_Var_Keys, tuple): L_P_List_Var_Keys = (L_P_List_Var_Keys,)
        if "%" not in L_P_Name: L_P_Name += "_%s" * len(L_P_List_Var_Keys)

        List_Var_Key_Part = L_P_List_Var_Keys[0]
        L_P_List_Var_Keys = L_P_List_Var_Keys[1:]
        Dict = {}
        if len(L_P_List_Var_Keys) == 0:
            for i in List_Var_Key_Part:
                Dict[i] = L_P_Variable_Class(L_P_Name % tuple(List_Initial_val + [str(i)]), L_P_LOW_LIMIT, L_P_HIGH_LIMIT, L_P_Category)
        else:
            for i in List_Var_Key_Part:
                Dict[i] = L_P_Variable_Class.dicts(L_P_Name, L_P_List_Var_Keys, L_P_LOW_LIMIT, L_P_HIGH_LIMIT, L_P_Category, List_Initial_val + [i])
        return Dict
    dicts = classmethod(dicts)

    def dict(self, L_P_Name, L_P_List_Var_Keys, L_P_LOW_LIMIT = None, L_P_HIGH_LIMIT = None, L_P_Category = L_P_CONTINUOUS):
        if not isinstance(L_P_List_Var_Keys, tuple): L_P_List_Var_Keys = (L_P_List_Var_Keys,)
        if "%" not in L_P_Name: L_P_Name += "_%s" * len(L_P_List_Var_Keys)

        Lists_Var_Keys = L_P_List_Var_Keys

        if len(L_P_List_Var_Keys)>1:
            # Cartesian product
            Result = []
            while len(Lists_Var_Keys):
                First_key = Lists_Var_Keys[-1]
                prtRES = []
                if Result:
                    if First_key:
                        for j in First_key:
                            prtRES.L_P_Extend_constraint([[j]+res for res in Result])
                    else:
                        prtRES = Result
                    Result = prtRES
                else:
                    Result = [[j] for j in First_key]
                Lists_Var_Keys = Lists_Var_Keys[:-1]
            index = [tuple(res) for res in Result]
        elif len(L_P_List_Var_Keys) == 1:
            index = L_P_List_Var_Keys[0]
        else:
            return {}

        Dict = {}
        for i in index:
         Dict[i] = self(L_P_Name % i, L_P_LOW_LIMIT, L_P_HIGH_LIMIT, L_P_Category)
        return Dict
    dict = classmethod(dict)

    def L_P_Get_LOW_Limit(self):
        return self.L_P_LOW_LIMIT

    def L_P_Get_HIGH_Limit(self):
        return self.L_P_HIGH_LIMIT

    def L_P_Set_Bound(self, low, up):
        self.L_P_LOW_LIMIT = low
        self.L_P_HIGH_LIMIT = up
        self.L_P_Modify = True

    def L_P_SET_POS_BOUND(self):
        self.L_P_Set_Bound(0, None)

    def value(self):
        return self.L_P_Variable_Val

    def L_P_Round_Val(self, Epsilon_Int = 1e-5, Epsilon = 1e-7):
        if self.L_P_Variable_Val is not None:
            if self.L_P_HIGH_LIMIT != None and self.L_P_Variable_Val > self.L_P_HIGH_LIMIT and self.L_P_Variable_Val <= self.L_P_HIGH_LIMIT + Epsilon:
                self.L_P_Variable_Val = self.L_P_HIGH_LIMIT
            elif self.L_P_LOW_LIMIT != None and self.L_P_Variable_Val < self.L_P_LOW_LIMIT and self.L_P_Variable_Val >= self.L_P_LOW_LIMIT - Epsilon:
                self.L_P_Variable_Val = self.L_P_LOW_LIMIT
            if self.L_P_Category == L_P_INT and abs(L_P_Round_Val(self.L_P_Variable_Val) - self.L_P_Variable_Val) <= Epsilon_Int:
                self.L_P_Variable_Val = L_P_Round_Val(self.L_P_Variable_Val)

    def L_P_Rounded_val(self, Epsilon = 1e-5):
        if self.L_P_Category == L_P_INT and self.L_P_Variable_Val != None \
            and abs(self.L_P_Variable_Val - L_P_Round_Val(self.L_P_Variable_Val)) <= Epsilon:
            return L_P_Round_Val(self.L_P_Variable_Val)
        else:
            return self.L_P_Variable_Val

    def L_P_DefaultorVal(self):
        if self.L_P_Variable_Val != None:
            return self.L_P_Variable_Val
        elif self.L_P_LOW_LIMIT != None:
            if self.L_P_HIGH_LIMIT != None:
                if 0 >= self.L_P_LOW_LIMIT and 0 <= self.L_P_HIGH_LIMIT:
                    return 0
                else:
                    if self.L_P_LOW_LIMIT >= 0:
                        return self.L_P_LOW_LIMIT
                    else:
                        return self.L_P_HIGH_LIMIT
            else:
                if 0 >= self.L_P_LOW_LIMIT:
                    return 0
                else:
                    return self.L_P_LOW_LIMIT
        elif self.L_P_HIGH_LIMIT != None:
            if 0 <= self.L_P_HIGH_LIMIT:
                return 0
            else:
                return self.L_P_HIGH_LIMIT
        else:
            return 0

    def L_P_Var_Valid_Checker(self, Epsilon):
        if self.L_P_Variable_Val == None: return False
        if self.L_P_HIGH_LIMIT != None and self.L_P_Variable_Val > self.L_P_HIGH_LIMIT + Epsilon:
            return False
        if self.L_P_LOW_LIMIT != None and self.L_P_Variable_Val < self.L_P_LOW_LIMIT - Epsilon:
            return False
        if self.L_P_Category == L_P_INT and abs(L_P_Round_Val(self.L_P_Variable_Val) - self.L_P_Variable_Val) > Epsilon:
            return False
        return True

    def L_P_Infeasible_Gap(self, mip = 1):
        if self.L_P_Variable_Val == None: raise ValueError("value of variable can not be None")
        if self.L_P_HIGH_LIMIT != None and self.L_P_Variable_Val > self.L_P_HIGH_LIMIT:
            return self.L_P_Variable_Val - self.L_P_HIGH_LIMIT
        if self.L_P_LOW_LIMIT != None and self.L_P_Variable_Val < self.L_P_LOW_LIMIT:
            return self.L_P_Variable_Val - self.L_P_LOW_LIMIT
        if mip and self.L_P_Category == L_P_INT and L_P_Round_Val(self.L_P_Variable_Val) - self.L_P_Variable_Val != 0:
            return L_P_Round_Val(self.L_P_Variable_Val) - self.L_P_Variable_Val
        return 0

    def L_P_Binary_Checker(self):
        return self.L_P_Category == L_P_INT and self.L_P_LOW_LIMIT == 0 and self.L_P_HIGH_LIMIT == 1

    def L_P_Integer_Checker(self):
        return self.L_P_Category == L_P_INT

    def L_P_NObound(self):
        return self.L_P_LOW_LIMIT == None and self.L_P_HIGH_LIMIT == None

    def L_P_constant_checker(self):
        return self.L_P_LOW_LIMIT != None and self.L_P_HIGH_LIMIT == self.L_P_LOW_LIMIT

    def L_P_Pos_Checker(self):
        return self.L_P_LOW_LIMIT == 0 and self.L_P_HIGH_LIMIT == None

    def L_P_Cplex_Var_format(self):
        if self.L_P_NObound(): return self.L_P_Name + " free"
        if self.L_P_constant_checker(): return self.L_P_Name + " = %.12g" % self.L_P_LOW_LIMIT
        if self.L_P_LOW_LIMIT == None:
            String_Limit= "-inf <= "
        # Note: CPLEX do not interpret integer L_P_variables_List without
        # explicit bounds
        elif (self.L_P_LOW_LIMIT == 0 and self.L_P_Category == L_P_CONTINUOUS):
            String_Limit = ""
        else:
            String_Limit= "%.12g <= " % self.L_P_LOW_LIMIT
        String_Limit += self.L_P_Name
        if self.L_P_HIGH_LIMIT != None:
            String_Limit+= " <= %.12g" % self.L_P_HIGH_LIMIT
        return String_Limit

    def L_P_Cplex_Fine_Expression(self, L_P_Name, L_P_CONST_VAL = 1):
        return L_P_AFFine_Expression(self).L_P_Cplex_Fine_Expression(L_P_Name, L_P_CONST_VAL)

    def __ne__(self, L_P_Other_Value):
        if isinstance(L_P_Other_Value, L_P_Basic_Element):
            return self.L_P_Name is not L_P_Other_Value.L_P_Name
        elif isinstance(L_P_Other_Value, L_P_AFFine_Expression):
            if L_P_Other_Value.L_P_Atomic_Express():
                return self is not L_P_Other_Value.L_P_ATOM()
            else:
                return 1
        else:
            return 1

    def L_P_Variable_Add_Constraint(self,L_P_ExtraVar_Exist):
        """adds a variable to the L_p_Constraints indicated by
        the LpConstraintVars in L_P_ExtraVar_Exist
        """
        for constraint, coeff in L_P_ExtraVar_Exist.items():
            constraint.L_P_Add_Var_Funct(self,coeff)

    def setInitialValue(self,val):
        """sets the initial value of the Variable to val
        may of may not be supported by the L_P_SOLVER need to be implemented
        """
        raise NotImplementedError


class L_P_AFFine_Expression(_DICT_TYPE):
    """
    A linear combination of :class:`LpVariables<L_P_Variable_Class>`.
    Can be initialised with the following:

    #.   L_P_ExtraVar_Exist = None:  an empty Expression
    #.   L_P_ExtraVar_Exist = dict: gives an L_P_expression with the values being the Constraint_Coefficients of the keys (order of terms is undetermined)
    #.   L_P_ExtraVar_Exist = list or generator of 2-tuples: it is equivalent to dict.items() which returns a list or tuple
    #.   L_P_ExtraVar_Exist = L_P_Basic_Element: an L_P_expression of length 1 with the coefficient 1
    #.   L_P_ExtraVar_Exist = L_P_Other_Value: the L_P_CONST_VAL is initialised as L_P_ExtraVar_Exist

    Examples:

       >>> f=hueslib.L_P_AFFine_Expression(hueslib.L_P_Basic_Element('x'))
       >>> f
       1*x + 0
       >>> y_name = ['y_0', 'y_1', 'y_2']
       >>> z = [hueslib.L_P_Variable_Class(y_name[i], L_P_LOW_LIMIT = 0, L_P_HIGH_LIMIT = 10) for i in range(3) ]
       >>> c = hueslib.L_P_AFFine_Expression([ (z[0],1), (z[1],-3), (z[2],4)])
       >>> c
       1*y_0 + -3*y_1 + 4*y_2 + 0
       >>>c.L_P_Atomic_Express()
       False
       >>>c.L_P_isValCONSTANT()
       False
       >>>c.L_P_ATOM()
       y_0
       >>>c.L_P_DefaultorVal()   #returns the default values
       0
       >>>x = hueslib.L_P_Variable_Class("x", 1, 5)
       >>>c.L_P_exp_ADD_TERM(x,"10")
       10*x + 1*y_0 + -3*y_1 + 4*y_2 + 0
       >>>h=c.L_P_Copy_funct()
       10*x + 1*y_0 + -3*y_1 + 4*y_2 + 0
       >>>c.SORT_keys_Inexp()
       [x, y_0, y_1, y_2]
       
    """
    #to remove illegal characters from the names like -+[] 
    trans = str.maketrans("-+[] ","_____")
    def L_P_Name_Setter(self,L_P_Name):
        if L_P_Name:
            self.L_P__name = str(L_P_Name).translate(self.trans)
        else:
            self.L_P__name = None

    def L_P_Name_Getter(self):
        return self.L_P__name

    L_P_Name = property(fget=L_P_Name_Getter, fset=L_P_Name_Setter)

    def __init__(self, L_P_ExtraVar_Exist = None, L_P_CONST_VAL = 0, L_P_Name = None):
        self.L_P_Name = L_P_Name
        if L_P_ExtraVar_Exist is None:
            L_P_ExtraVar_Exist = {}
        if isinstance(L_P_ExtraVar_Exist, L_P_AFFine_Expression):
            # Will not use copy function the Name
            self.L_P_CONST_VAL = L_P_ExtraVar_Exist.L_P_CONST_VAL
            super(L_P_AFFine_Expression, self).__init__(list(L_P_ExtraVar_Exist.items()))
        elif isinstance(L_P_ExtraVar_Exist, dict):
            self.L_P_CONST_VAL = L_P_CONST_VAL
            super(L_P_AFFine_Expression, self).__init__(list(L_P_ExtraVar_Exist.items()))
        elif isinstance(L_P_ExtraVar_Exist, Iterable):
            self.L_P_CONST_VAL = L_P_CONST_VAL
            super(L_P_AFFine_Expression, self).__init__(L_P_ExtraVar_Exist)
        elif isinstance(L_P_ExtraVar_Exist,L_P_Basic_Element):
            self.L_P_CONST_VAL = 0
            super(L_P_AFFine_Expression, self).__init__( [(L_P_ExtraVar_Exist, 1)])
        else:
            self.L_P_CONST_VAL = L_P_ExtraVar_Exist
            super(L_P_AFFine_Expression, self).__init__()

    # Proxy functions for variable list 

    def L_P_Atomic_Express(self):
        return len(self) == 1 and self.L_P_CONST_VAL == 0 and list(self.values())[0] == 1

    def L_P_isValCONSTANT(self):
        return len(self) == 0
        #reurns atomic or first variable in expressions
    def L_P_ATOM(self):
        return list(self.keys())[0]

    # Functions on expressions

    def __bool__(self):
        return (float(self.L_P_CONST_VAL) != 0.0) or (len(self) > 0)
    #print the value of the expression
    def value(self):
        val = self.L_P_CONST_VAL
        for v,x in self.items():
            if v.L_P_Variable_Val is None:
                return None
            val += v.L_P_Variable_Val * x
        return val

    def L_P_DefaultorVal(self):
        val = self.L_P_CONST_VAL
        for v,x in self.items():
            val += v.L_P_DefaultorVal() * x
        return val

    def L_P_exp_ADD_TERM(self, key, value):
            y = self.get(key, 0)
            if y:
                y += value
                self[key] = y
            else:
                self[key] = value

    def L_P_Empty_Copy(self):
        return L_P_AFFine_Expression()

    def L_P_Copy_funct(self):
        """Make a Copy of self except the when the linear programming name is reset"""
        # Will not use L_P_Copy_funct with the Linear Programming name
        return L_P_AFFine_Expression(self)

    def __str__(self, L_P_CONST_VAL = 1):
        Str_Rep = ""
        for v in self.SORT_keys_Inexp():
            val = self[v]
            if val<0:
                if Str_Rep != "": Str_Rep += " - "
                else: Str_Rep += "-"
                val = -val
            elif Str_Rep != "": Str_Rep += " + "
            if val == 1: Str_Rep += str(v)
            else: Str_Rep += str(val) + "*" + str(v)
        if L_P_CONST_VAL:
            if Str_Rep == "":
                Str_Rep = str(self.L_P_CONST_VAL)
            else:
                if self.L_P_CONST_VAL < 0: Str_Rep += " - " + str(-self.L_P_CONST_VAL)
                elif self.L_P_CONST_VAL > 0: Str_Rep += " + " + str(self.L_P_CONST_VAL)
        elif Str_Rep == "":
            Str_Rep = "0"
        return Str_Rep

    def SORT_keys_Inexp(self):
        """
        returns the list of keys sorted by Milp variable name 
        """
        result = [(vari.L_P_Name, vari) for vari in self.keys()]
        result.sort()
        result = [vari for _, vari in result]
        return result

    def __repr__(self):
        listVal = [str(self[vari]) + "*" + str(vari)
                        for vari in self.SORT_keys_Inexp()]
        listVal.append(str(self.L_P_CONST_VAL))
        s = " + ".join(listVal)
        return s

    @staticmethod
    def char_count_liststr(Line_lp):
        #counts the characters in a list of strings
        return sum(len(u) for u in Line_lp)

    def L_P_Cplex_Variable_Only(self, L_P_Name):
        """
        helper for L_P_Cplex_Fine_Expression
        """
        result = []
        Line_lp = ["%s:" % L_P_Name]
        notFirst = 0
        variabs = self.SORT_keys_Inexp()
        for v in variabs:
            signvalue = self[v]
            if signvalue < 0:
                sign = " -"
                signvalue = -signvalue
            elif notFirst:
                sign = " +"
            else:
                sign = ""
            notFirst = 1
            if signvalue == 1:
                L_P_term = "%s %s" %(sign, v.L_P_Name)
            else:
                L_P_term = "%s %.12g %s" % (sign, signvalue, v.L_P_Name)

            if self.char_count_liststr(Line_lp) + len(L_P_term) > Lp_Cplex_Solver_MAX_LINELENGTH:
                result += ["".join(Line_lp)]
                Line_lp = [L_P_term]
            else:
                Line_lp += [L_P_term]
        return result, Line_lp

    def L_P_Cplex_Fine_Expression(self, L_P_Name, L_P_CONST_VAL = 1):
        """
        returns a string that represents the Affine Expression in lp format
        """
        #refactored to use a list for speed in iron python
        result, Line_lp = self.L_P_Cplex_Variable_Only(L_P_Name)
        if not self:
            L_P_term = " %s" % self.L_P_CONST_VAL
        else:
            L_P_term = ""
            if L_P_CONST_VAL:
                if self.L_P_CONST_VAL < 0:
                    L_P_term = " - %s" % (-self.L_P_CONST_VAL)
                elif self.L_P_CONST_VAL > 0:
                    L_P_term = " + %s" % self.L_P_CONST_VAL
        if self.char_count_liststr(Line_lp) + len(L_P_term) > Lp_Cplex_Solver_MAX_LINELENGTH:
            result += ["".join(Line_lp)]
            Line_lp = [L_P_term]
        else:
            Line_lp += [L_P_term]
        result += ["".join(Line_lp)]
        result = "%s\n" % "\n".join(result)
        return result

    def IN_PLACE_ADDITION(self, L_P_Other_Value):
        if L_P_Other_Value is 0: return self
        if L_P_Other_Value is None: return self
        if isinstance(L_P_Other_Value,L_P_Basic_Element):
            self.L_P_exp_ADD_TERM(L_P_Other_Value, 1)
        elif isinstance(L_P_Other_Value,L_P_AFFine_Expression):
            self.L_P_CONST_VAL += L_P_Other_Value.L_P_CONST_VAL
            for v,x in L_P_Other_Value.items():
                self.L_P_exp_ADD_TERM(v, x)
        elif isinstance(L_P_Other_Value,dict):
            for L_P_ExtraVar_Exist in L_P_Other_Value.values():
                self.IN_PLACE_ADDITION(L_P_ExtraVar_Exist)
        elif (isinstance(L_P_Other_Value,list)
              or isinstance(L_P_Other_Value, Iterable)):
           for L_P_ExtraVar_Exist in L_P_Other_Value:
                self.IN_PLACE_ADDITION(L_P_ExtraVar_Exist)
        else:
            self.L_P_CONST_VAL += L_P_Other_Value
        return self

    def IN_PLACE_Subtract(self, L_P_Other_Value):
        if L_P_Other_Value is 0: return self
        if L_P_Other_Value is None: return self
        if isinstance(L_P_Other_Value,L_P_Basic_Element):
            self.L_P_exp_ADD_TERM(L_P_Other_Value, -1)
        elif isinstance(L_P_Other_Value,L_P_AFFine_Expression):
            self.L_P_CONST_VAL -= L_P_Other_Value.L_P_CONST_VAL
            for v,x in L_P_Other_Value.items():
                self.L_P_exp_ADD_TERM(v, -x)
        elif isinstance(L_P_Other_Value,dict):
            for L_P_ExtraVar_Exist in L_P_Other_Value.values():
                self.IN_PLACE_Subtract(L_P_ExtraVar_Exist)
        elif (isinstance(L_P_Other_Value,list)
              or isinstance(L_P_Other_Value, Iterable)):
            for L_P_ExtraVar_Exist in L_P_Other_Value:
                self.IN_PLACE_Subtract(L_P_ExtraVar_Exist)
        else:
            self.L_P_CONST_VAL -= L_P_Other_Value
        return self

    def __neg__(self):
        L_P_ExtraVar_Exist = self.L_P_Empty_Copy()
        L_P_ExtraVar_Exist.L_P_CONST_VAL = - self.L_P_CONST_VAL
        for v,x in self.items():
            L_P_ExtraVar_Exist[v] = - x
        return L_P_ExtraVar_Exist

    def __pos__(self):
        return self

    def __add__(self, L_P_Other_Value):
        return self.L_P_Copy_funct().IN_PLACE_ADDITION(L_P_Other_Value)

    def __radd__(self, L_P_Other_Value):
        return self.L_P_Copy_funct().IN_PLACE_ADDITION(L_P_Other_Value)

    def __iadd__(self, L_P_Other_Value):
        return self.IN_PLACE_ADDITION(L_P_Other_Value)

    def __sub__(self, L_P_Other_Value):
        return self.L_P_Copy_funct().IN_PLACE_Subtract(L_P_Other_Value)

    def __rsub__(self, L_P_Other_Value):
        return (-self).IN_PLACE_ADDITION(L_P_Other_Value)

    def __isub__(self, L_P_Other_Value):
        return (self).IN_PLACE_Subtract(L_P_Other_Value)


    def __mul__(self, L_P_Other_Value):
        L_P_ExtraVar_Exist = self.L_P_Empty_Copy()
        if isinstance(L_P_Other_Value,L_P_AFFine_Expression):
            L_P_ExtraVar_Exist.L_P_CONST_VAL = self.L_P_CONST_VAL * L_P_Other_Value.L_P_CONST_VAL
            if len(L_P_Other_Value):
                if len(self):
                    raise TypeError("Non-L_P_CONST_VAL expressions cannot be multiplied")
                else:
                    c = self.L_P_CONST_VAL
                    if c != 0:
                        for v,x in L_P_Other_Value.items():
                            L_P_ExtraVar_Exist[v] = c * x
            else:
                c = L_P_Other_Value.L_P_CONST_VAL
                if c != 0:
                    for v,x in self.items():
                        L_P_ExtraVar_Exist[v] = c * x
        elif isinstance(L_P_Other_Value,L_P_Variable_Class):
            return self * L_P_AFFine_Expression(L_P_Other_Value)
        else:
            if L_P_Other_Value != 0:
                L_P_ExtraVar_Exist.L_P_CONST_VAL = self.L_P_CONST_VAL * L_P_Other_Value
                for v,x in self.items():
                    L_P_ExtraVar_Exist[v] = L_P_Other_Value * x
        return L_P_ExtraVar_Exist

    def __rmul__(self, L_P_Other_Value):
        return self * L_P_Other_Value

    def __div__(self, L_P_Other_Value):
        if isinstance(L_P_Other_Value,L_P_AFFine_Expression) or isinstance(L_P_Other_Value,L_P_Variable_Class):
            if len(L_P_Other_Value):
                raise TypeError("Expressions cannot be divided by a non-L_P_CONST_VAL L_P_expression")
            L_P_Other_Value = L_P_Other_Value.L_P_CONST_VAL
        L_P_ExtraVar_Exist = self.L_P_Empty_Copy()
        L_P_ExtraVar_Exist.L_P_CONST_VAL = self.L_P_CONST_VAL / L_P_Other_Value
        for v,x in self.items():
            L_P_ExtraVar_Exist[v] = x / L_P_Other_Value
        return L_P_ExtraVar_Exist

    def __truediv__(self, L_P_Other_Value):
        if isinstance(L_P_Other_Value,L_P_AFFine_Expression) or isinstance(L_P_Other_Value,L_P_Variable_Class):
            if len(L_P_Other_Value):
                raise TypeError("Expressions cannot be divided by a non-L_P_CONST_VAL L_P_expression")
            L_P_Other_Value = L_P_Other_Value.L_P_CONST_VAL
        L_P_ExtraVar_Exist = self.L_P_Empty_Copy()
        L_P_ExtraVar_Exist.L_P_CONST_VAL = self.L_P_CONST_VAL / L_P_Other_Value
        for v,x in self.items():
            L_P_ExtraVar_Exist[v] = x / L_P_Other_Value
        return L_P_ExtraVar_Exist

    def __rdiv__(self, L_P_Other_Value):
        L_P_ExtraVar_Exist = self.L_P_Empty_Copy()
        if len(self):
            raise TypeError("Expressions cannot be divided by a non-L_P_CONST_VAL L_P_expression")
        c = self.L_P_CONST_VAL
        if isinstance(L_P_Other_Value,L_P_AFFine_Expression):
            L_P_ExtraVar_Exist.L_P_CONST_VAL = L_P_Other_Value.L_P_CONST_VAL / c
            for v,x in L_P_Other_Value.items():
                L_P_ExtraVar_Exist[v] = x / c
        else:
            L_P_ExtraVar_Exist.L_P_CONST_VAL = L_P_Other_Value / c
        return L_P_ExtraVar_Exist

    def __le__(self, L_P_Other_Value):
        return L_P_Constraint_CLASS(self - L_P_Other_Value, L_P_LessThanEqu_Constraint)

    def __ge__(self, L_P_Other_Value):
        return L_P_Constraint_CLASS(self - L_P_Other_Value, L_P_GreatThanEqu_Constraint)

    def __eq__(self, L_P_Other_Value):
        return L_P_Constraint_CLASS(self - L_P_Other_Value, L_P_Equality_Constraint)

class L_P_Constraint_CLASS(L_P_AFFine_Expression):
    """An LP constraint"""
    def __init__(self, L_P_ExtraVar_Exist = None, EQ_GE_LE_TYPE = L_P_Equality_Constraint,
                  L_P_Name = None, Val_Rhs = None):
        """
        :PARAMETERS_DEFINED  L_P_ExtraVar_Exist: an instance of :class:`L_P_AFFine_Expression`
        :PARAMETERS_DEFINED  EQ_GE_LE_TYPE: one of :data:`L_P_Equality_Constraint`, :data:`~L_P_GreatThanEqu_Constraint`, :data:`~L_P_LessThanEqu_Constraint` (0, 1, -1 respectively)
        :PARAMETERS_DEFINED  L_P_Name: identifying string
        :PARAMETERS_DEFINED  Val_Rhs: numerical value of constraint target
        """
        L_P_AFFine_Expression.__init__(self, L_P_ExtraVar_Exist, L_P_Name = L_P_Name)
        if Val_Rhs is not None:
            self.L_P_CONST_VAL = - Val_Rhs
        self.EQ_GE_LE_TYPE = EQ_GE_LE_TYPE
        self.pi = None
        self.Val_slack = None
        self.L_P_Modify = True

    def L_P_Get_LOW_Limit(self):
        if ( (self.EQ_GE_LE_TYPE == L_P_GreatThanEqu_Constraint) or
             (self.EQ_GE_LE_TYPE == L_P_Equality_Constraint) ):
            return -self.L_P_CONST_VAL
        else:
            return None

    def L_P_Get_HIGH_Limit(self):
        if ( (self.EQ_GE_LE_TYPE == L_P_LessThanEqu_Constraint) or
             (self.EQ_GE_LE_TYPE == L_P_Equality_Constraint) ):
            return -self.L_P_CONST_VAL
        else:
            return None

    def __str__(self):
        Str_rep = L_P_AFFine_Expression.__str__(self, 0)
        if self.EQ_GE_LE_TYPE is not None:
            Str_rep += " " + LpConstraintSenses[self.EQ_GE_LE_TYPE] + " " + str(-self.L_P_CONST_VAL)
        return Str_rep

    def L_P_CPLEX_asConstraint(self, L_P_Name):
        """
        Returns a constraint as a string
        """
        result, Line_lp = self.L_P_Cplex_Variable_Only(L_P_Name)
        if not list(self.keys()):
            Line_lp += ["0"]
        c = -self.L_P_CONST_VAL
        if c == 0:
            c = 0 # Supress sign
        L_P_term = " %s %.12g" % (LpConstraintSenses[self.EQ_GE_LE_TYPE], c)
        if self.char_count_liststr(Line_lp)+len(L_P_term) > Lp_Cplex_Solver_MAX_LINELENGTH:
            result += ["".join(Line_lp)]
            Line_lp = [L_P_term]
        else:
            Line_lp += [L_P_term]
        result += ["".join(Line_lp)]
        result = "%s\n" % "\n".join(result)
        return result

    def Rhs_modified(self, RHS):
        """
        alters the RHS of a constraint so that it can be L_P_Modify in a resolve
        """
        self.L_P_CONST_VAL = -RHS
        self.L_P_Modify = True

    def __repr__(self):
        s = L_P_AFFine_Expression.__repr__(self)
        if self.EQ_GE_LE_TYPE is not None:
            s += " " + LpConstraintSenses[self.EQ_GE_LE_TYPE] + " 0"
        return s

    def L_P_Copy_funct(self):
        """Make a L_P_Copy_funct of self"""
        return L_P_Constraint_CLASS(self, self.EQ_GE_LE_TYPE)

    def L_P_Empty_Copy(self):
        return L_P_Constraint_CLASS(EQ_GE_LE_TYPE = self.EQ_GE_LE_TYPE)

    def IN_PLACE_ADDITION(self, L_P_Other_Value):
        if isinstance(L_P_Other_Value,L_P_Constraint_CLASS):
            if self.EQ_GE_LE_TYPE * L_P_Other_Value.EQ_GE_LE_TYPE >= 0:
                L_P_AFFine_Expression.IN_PLACE_ADDITION(self, L_P_Other_Value)
                self.EQ_GE_LE_TYPE |= L_P_Other_Value.EQ_GE_LE_TYPE
            else:
                L_P_AFFine_Expression.IN_PLACE_Subtract(self, L_P_Other_Value)
                self.EQ_GE_LE_TYPE |= - L_P_Other_Value.EQ_GE_LE_TYPE
        elif isinstance(L_P_Other_Value,list):
            for L_P_ExtraVar_Exist in L_P_Other_Value:
                self.IN_PLACE_ADDITION(L_P_ExtraVar_Exist)
        else:
            L_P_AFFine_Expression.IN_PLACE_ADDITION(self, L_P_Other_Value)
            #raise TypeError, "Constraints and Expressions cannot be added"
        return self

    def IN_PLACE_Subtract(self, L_P_Other_Value):
        if isinstance(L_P_Other_Value,L_P_Constraint_CLASS):
            if self.EQ_GE_LE_TYPE * L_P_Other_Value.EQ_GE_LE_TYPE <= 0:
                L_P_AFFine_Expression.IN_PLACE_Subtract(self, L_P_Other_Value)
                self.EQ_GE_LE_TYPE |= - L_P_Other_Value.EQ_GE_LE_TYPE
            else:
                L_P_AFFine_Expression.IN_PLACE_ADDITION(self, L_P_Other_Value)
                self.EQ_GE_LE_TYPE |= L_P_Other_Value.EQ_GE_LE_TYPE
        elif isinstance(L_P_Other_Value,list):
            for L_P_ExtraVar_Exist in L_P_Other_Value:
                self.IN_PLACE_Subtract(L_P_ExtraVar_Exist)
        else:
            L_P_AFFine_Expression.IN_PLACE_Subtract(self, L_P_Other_Value)
            #raise TypeError, "Constraints and Expressions cannot be added"
        return self

    def __neg__(self):
        c = L_P_AFFine_Expression.__neg__(self)
        c.EQ_GE_LE_TYPE = - c.EQ_GE_LE_TYPE
        return c

    def __add__(self, L_P_Other_Value):
        return self.L_P_Copy_funct().IN_PLACE_ADDITION(L_P_Other_Value)

    def __radd__(self, L_P_Other_Value):
        return self.L_P_Copy_funct().IN_PLACE_ADDITION(L_P_Other_Value)

    def __sub__(self, L_P_Other_Value):
        return self.L_P_Copy_funct().IN_PLACE_Subtract(L_P_Other_Value)

    def __rsub__(self, L_P_Other_Value):
        return (-self).IN_PLACE_ADDITION(L_P_Other_Value)

    def __mul__(self, L_P_Other_Value):
        if isinstance(L_P_Other_Value,L_P_Constraint_CLASS):
            c = L_P_AFFine_Expression.__mul__(self, L_P_Other_Value)
            if c.EQ_GE_LE_TYPE == 0:
                c.EQ_GE_LE_TYPE = L_P_Other_Value.EQ_GE_LE_TYPE
            elif L_P_Other_Value.EQ_GE_LE_TYPE != 0:
                c.EQ_GE_LE_TYPE *= L_P_Other_Value.EQ_GE_LE_TYPE
            return c
        else:
            return L_P_AFFine_Expression.__mul__(self, L_P_Other_Value)

    def __rmul__(self, L_P_Other_Value):
        return self * L_P_Other_Value

    def __div__(self, L_P_Other_Value):
        if isinstance(L_P_Other_Value,L_P_Constraint_CLASS):
            c = L_P_AFFine_Expression.__div__(self, L_P_Other_Value)
            if c.EQ_GE_LE_TYPE == 0:
                c.EQ_GE_LE_TYPE = L_P_Other_Value.EQ_GE_LE_TYPE
            elif L_P_Other_Value.EQ_GE_LE_TYPE != 0:
                c.EQ_GE_LE_TYPE *= L_P_Other_Value.EQ_GE_LE_TYPE
            return c
        else:
            return L_P_AFFine_Expression.__mul__(self, L_P_Other_Value)

    def __rdiv__(self, L_P_Other_Value):
        if isinstance(L_P_Other_Value,L_P_Constraint_CLASS):
            c = L_P_AFFine_Expression.__rdiv__(self, L_P_Other_Value)
            if c.EQ_GE_LE_TYPE == 0:
                c.EQ_GE_LE_TYPE = L_P_Other_Value.EQ_GE_LE_TYPE
            elif L_P_Other_Value.EQ_GE_LE_TYPE != 0:
                c.EQ_GE_LE_TYPE *= L_P_Other_Value.EQ_GE_LE_TYPE
            return c
        else:
            return L_P_AFFine_Expression.__mul__(self, L_P_Other_Value)

    def L_P_Var_Valid_Checker(self, Epsilon = 0):
        val = self.value()
        if self.EQ_GE_LE_TYPE == L_P_Equality_Constraint: return abs(val) <= Epsilon
        else: return val * self.EQ_GE_LE_TYPE >= - Epsilon

    def Elastic_L_Pproblem(self, *args, **kwargs):
        """
        Builds an elastic linear programming subproblem by adding L_P_variables_List to a hard constraint

        uses ealstix fixed lp problem function
        """
        return Elastic_fixed_L_Pproblem(self, *args, **kwargs)

class L_P_Fract_Constraint(L_P_Constraint_CLASS):
    """
    Creates a constraint that enforces a fraction requirement a/b = c
    """
    def __init__(self, L_P_num, L_P_Denom = None, EQ_GE_LE_TYPE = L_P_Equality_Constraint,
                 RHS = 1.0, L_P_Name = None,
                 Comp = None):
        """
        creates a fraction Constraint to model L_p_Constraints of
        the nature
        L_P_num/L_P_Denom {==, >=, <=} RHS
        L_P_num/(L_P_num + Comp) {==, >=, <=} RHS

        :PARAMETERS_DEFINED  L_P_num: the top of the fraction
        :PARAMETERS_DEFINED  L_P_Denom: as described above
        :PARAMETERS_DEFINED  EQ_GE_LE_TYPE: the EQ_GE_LE_TYPE of the relation of the constraint
        :PARAMETERS_DEFINED  RHS: the target fraction value
        :PARAMETERS_DEFINED  Comp: as described above
        """
        self.L_P_num = L_P_num
        if L_P_Denom is None and Comp is not None:
            self.Comp = Comp
            self.L_P_Denom = L_P_num + Comp
        elif L_P_Denom is not None and Comp is None:
            self.L_P_Denom = L_P_Denom
            self.Comp = L_P_Denom - L_P_num
        else:
            self.L_P_Denom = L_P_Denom
            self.Comp = Comp
        lhs = self.L_P_num - RHS * self.L_P_Denom
        L_P_Constraint_CLASS.__init__(self, lhs,
              EQ_GE_LE_TYPE = EQ_GE_LE_TYPE, Val_Rhs = 0, L_P_Name = L_P_Name)
        self.RHS = RHS

    def findLHSValue(self):
        """
        Determines the  value of the constraints as in solution 
        """
        if abs(value(self.L_P_Denom))>= EPS:
            return value(self.L_P_num)/value(self.L_P_Denom)
        else:
            if abs(value(self.L_P_num))<= EPS:
                #zero divided by zero will return 1
                return 1.0
            else:
                raise ZeroDivisionError

    def Elastic_L_Pproblem(self, *args, **kwargs):
        """
        By splitting the hard constraints make elastic subproblems

        uses FractionElasticSubProblem
        """
        return FractionElasticSubProblem(self, *args, **kwargs)

class L_P_Constraint_Var_Class(L_P_Basic_Element):
    """A Constraint that can be made variable by construction of milp problem in column form
    """
    def __init__(self, L_P_Name = None ,EQ_GE_LE_TYPE = None,
                 Val_Rhs = None, L_P_ExtraVar_Exist = None):
        L_P_Basic_Element.__init__(self,L_P_Name)
        self.constraint = L_P_Constraint_CLASS(L_P_Name = self.L_P_Name, EQ_GE_LE_TYPE = EQ_GE_LE_TYPE,
                                       Val_Rhs = Val_Rhs , L_P_ExtraVar_Exist = L_P_ExtraVar_Exist)

    def L_P_Add_Var_Funct(self, var, coeff):
        """
        Adds a variable to the constraint with the
        activity coeff
        """
        self.constraint.L_P_exp_ADD_TERM(var, coeff)

    def value(self):
        return self.constraint.value()

class L_P_Problem_class(object):
    """An LP Problem"""
    def __init__(self, L_P_Name = "NoName", EQ_GE_LE_TYPE = L_P_MINIMIZE_PROB):
        """
        Creates an LP Problem

        This function creates a new LP Problem  with the specified associated parameters

        :PARAMETERS_DEFINED  L_P_Name: L_P_Name of the problem used in the output .lp file
        :PARAMETERS_DEFINED  EQ_GE_LE_TYPE: of the LP problem L_P_Objective.  \
                Either :data:`~L_P_MINIMIZE_PROB` (default) \
                or :data:`~L_P_MAXIMIZE_PROB`.
        :return: An LP Problem
        """
        self.L_P_Objective = None
        self.L_p_Constraints = _DICT_TYPE()
        self.L_P_Name = L_P_Name
        self.EQ_GE_LE_TYPE = EQ_GE_LE_TYPE
        self.L_p_SOL1 = {}
        self.L_p_SOL2 = {}
        self.L_p_Status = L_P_Stat_Notsolve
        self.NO_OverLap_COND = 1
        self.L_P_SOLVER = None
        self.L_P_Initial_Values = {}
        self.L_P_Modify_Variables = []
        self.L_P_Modify_Constraints = []
        self.L_P_RESOLVED = False
        self.L_P_Variable_lists = []
        self.L_P_VARIABLES_IDS = {}  #old school using dict.keys() for a set
        self.L_P_Var_dummy = None


        # locals
        self.L_P_UNUSED_CONSTRAINTS = 0

    def __repr__(self):
        Str_lp_prob = self.L_P_Name+":\n"
        if self.EQ_GE_LE_TYPE == 1:
            Str_lp_prob += "MINIMIZE\n"
        else:
            Str_lp_prob += "MAXIMIZE\n"
        Str_lp_prob += repr(self.L_P_Objective) +"\n"

        if self.L_p_Constraints:
            Str_lp_prob += "SUBJECT TO\n"
            for n, c in self.L_p_Constraints.items():
                Str_lp_prob += c.L_P_CPLEX_asConstraint(n) +"\n"
        Str_lp_prob += "VARIABLES\n"
        for v in self.L_P_variables_List():
            Str_lp_prob += v.L_P_Cplex_Var_format() + " " + L_P_Diff_Categories[v.L_P_Category] + "\n"
        return Str_lp_prob

    def L_P_Copy_funct(self):
        """Make a L_P_Copy_funct of self. Expressions are copied by reference"""
        lpcopy = L_P_Problem_class(L_P_Name = self.L_P_Name, EQ_GE_LE_TYPE = self.EQ_GE_LE_TYPE)
        lpcopy.L_P_Objective = self.L_P_Objective
        lpcopy.L_p_Constraints = self.L_p_Constraints.L_P_Copy_funct()
        lpcopy.L_p_SOL1 = self.L_p_SOL1.L_P_Copy_funct()
        lpcopy.L_p_SOL2 = self.L_p_SOL2.L_P_Copy_funct()
        return lpcopy

    def deepcopy(self):
        """Make a L_P_Copy_funct of self. Expressions are copied by value"""
        lpcopy = L_P_Problem_class(L_P_Name = self.L_P_Name, EQ_GE_LE_TYPE = self.EQ_GE_LE_TYPE)
        if self.L_P_Objective is not None:
            lpcopy.L_P_Objective = self.L_P_Objective.L_P_Copy_funct()
        lpcopy.L_p_Constraints = {}
        for k,v in self.L_p_Constraints.items():
            lpcopy.L_p_Constraints[k] = v.L_P_Copy_funct()
        lpcopy.L_p_SOL1 = self.L_p_SOL1.L_P_Copy_funct()
        lpcopy.L_p_SOL2 = self.L_p_SOL2.L_P_Copy_funct()
        return lpcopy

    def Normalised_Var_NAMES(self):
        L_P_Constraints_Names = {}
        constraint_Eq_no = 0
        for k in self.L_p_Constraints:
            L_P_Constraints_Names[k] = "C%07d" % constraint_Eq_no
            constraint_Eq_no += 1
        variablesNames = {}
        constraint_Eq_no = 0
        for k in self.L_P_variables_List():
            variablesNames[k.L_P_Name] = "X%07d" % constraint_Eq_no
            constraint_Eq_no += 1
        return L_P_Constraints_Names, variablesNames, "OBJ"

    def ISMILP(self):
        for v in self.L_P_variables_List():
            if v.L_P_Category == L_P_INT: return 1
        return 0

    def L_P_RoundS_Solutions(self, Epsilon_Int = 1e-5, Epsilon = 1e-7):
        """
        Rounds the lp L_P_variables_List

        Inputs:
            - none

        Side Effects:
            - The lp L_P_variables_List are rounded
        """
        for v in self.L_P_variables_List():
            v.L_P_Round_Val(Epsilon_Int, Epsilon)

    def Notused_Constraint(self):
        self.L_P_UNUSED_CONSTRAINTS += 1
        while 1:
            str_r = "_C%d" % self.L_P_UNUSED_CONSTRAINTS
            if str_r not in self.L_p_Constraints: break
            self.L_P_UNUSED_CONSTRAINTS += 1
        return str_r

    def L_P_Var_Valid_Checker(self, Epsilon = 0):
        for v in self.L_P_variables_List():
            if not v.L_P_Var_Valid_Checker(Epsilon): return False
        for c in self.L_p_Constraints.values():
            if not c.L_P_Var_Valid_Checker(Epsilon): return False
        else:
            return True

    def L_P_Infeasible_Gap(self, mip = 1):
        L_P_Gaps = 0
        for v in self.L_P_variables_List():
            L_P_Gaps = max(abs(v.L_P_Infeasible_Gap(mip)), L_P_Gaps)
        for c in self.L_p_Constraints.values():
            if not c.L_P_Var_Valid_Checker(0):
                L_P_Gaps = max(abs(c.value()), L_P_Gaps)
        return L_P_Gaps

    def L_P_Add_Var_Funct(self, variable):
        """
        Adds a variable to the problem before a constraint is added

        @param variable: the variable to be added
        """
        if id(variable) not in self.L_P_VARIABLES_IDS:
            self.L_P_Variable_lists.append(variable)
            self.L_P_VARIABLES_IDS[id(variable)] = variable

    def L_P_add_Variables(self, L_P_variables_List):
        """
        Adds L_P_variables_List to the problem before a constraint is added

        @param L_P_variables_List: the L_P_variables_List to be added
        """
        for v in L_P_variables_List:
            self.L_P_Add_Var_Funct(v)

    def L_P_variables_List(self):
        """
        Returns a list of the problem L_P_variables_List

        Inputs:
            - none

        Returns:
            - A list of the problem L_P_variables_List
        """
        if self.L_P_Objective:
            self.L_P_add_Variables(list(self.L_P_Objective.keys()))
        for c in self.L_p_Constraints.values():
            self.L_P_add_Variables(list(c.keys()))
        L_P_variables_List = self.L_P_Variable_lists
        #sort the varibles DSU
        L_P_variables_List = [[v.L_P_Name, v] for v in L_P_variables_List]
        L_P_variables_List.sort()
        L_P_variables_List = [v for _, v in L_P_variables_List]
        return L_P_variables_List

    def L_P_Variables_Dictionary(self):
        L_P_variables_List = {}
        if self.L_P_Objective:
            for v in self.L_P_Objective:
                L_P_variables_List[v.L_P_Name] = v
        for c in list(self.L_p_Constraints.values()):
            for v in c:
                L_P_variables_List[v.L_P_Name] = v
        return L_P_variables_List

    def L_P_ADD_method(self, constraint, L_P_Name = None):
        self.L_P_Constraint_ADD(constraint, L_P_Name)

    def L_P_Constraint_ADD(self, constraint, L_P_Name = None):
        if not isinstance(constraint, L_P_Constraint_CLASS):
            raise TypeError("Can only L_P_ADD_method L_P_Constraint_CLASS objects")
        if L_P_Name:
            constraint.L_P_Name = L_P_Name
        try:
            if constraint.L_P_Name:
                L_P_Name = constraint.L_P_Name
            else:
                L_P_Name = self.Notused_Constraint()
        except AttributeError:
            raise TypeError("Can only L_P_ADD_method L_P_Constraint_CLASS objects")
            #removed as this test fails for empty L_p_Constraints
#        if len(constraint) == 0:
#            if not constraint.L_P_Var_Valid_Checker():
#                raise ValueError, "Cannot L_P_ADD_method false L_p_Constraints"
        if L_P_Name in self.L_p_Constraints:
            if self.NO_OverLap_COND:
                raise Hues_L_P_Error("overlapping constraint names: " + L_P_Name)
            else:
                print("Warning: overlapping constraint names:", L_P_Name)
        self.L_p_Constraints[L_P_Name] = constraint
        self.L_P_Modify_Constraints.append(constraint)
        self.L_P_add_Variables(list(constraint.keys()))

    def Objective_Setter_lp(self,obj):
        """
        Sets the input variable as the L_P_Objective function. Used in Columnwise Modelling

        :PARAMETERS_DEFINED  obj: the L_P_Objective function of type :class:`L_P_Constraint_Var_Class`

        Side Effects:
            - The L_P_Objective function is set
        """
        if isinstance(obj, L_P_Variable_Class):
            # allows the user to L_P_ADD_method a L_P_Variable_Class as an L_P_Objective
            obj = obj + 0.0
        try:
            obj = obj.constraint
            L_P_Name = obj.L_P_Name
        except AttributeError:
            L_P_Name = None
        self.L_P_Objective = obj
        self.L_P_Objective.L_P_Name = L_P_Name
        self.L_P_RESOLVED = False

    def __iadd__(self, L_P_Other_Value):
        if isinstance(L_P_Other_Value, tuple):
            L_P_Other_Value, L_P_Name = L_P_Other_Value
        else:
            L_P_Name = None
        if L_P_Other_Value is True:
            return self
        if isinstance(L_P_Other_Value, L_P_Constraint_Var_Class):
            self.L_P_Constraint_ADD(L_P_Other_Value.constraint)
        elif isinstance(L_P_Other_Value, L_P_Constraint_CLASS):
            self.L_P_Constraint_ADD(L_P_Other_Value, L_P_Name)
        elif isinstance(L_P_Other_Value, L_P_AFFine_Expression):
            self.L_P_Objective = L_P_Other_Value
            self.L_P_Objective.L_P_Name = L_P_Name
        elif isinstance(L_P_Other_Value, L_P_Variable_Class) or isinstance(L_P_Other_Value, (int, float)):
            self.L_P_Objective = L_P_AFFine_Expression(L_P_Other_Value)
            self.L_P_Objective.L_P_Name = L_P_Name
        else:
            raise TypeError("Can only L_P_ADD_method L_P_Constraint_Var_Class, L_P_Constraint_CLASS, L_P_AFFine_Expression or True objects")
        return self

    def L_P_Extend_constraint(self, L_P_Other_Value, use_objective = True):
        """
        extends an L_P_Problem_class by adding L_p_Constraints either from a dictionary
        a tuple or another L_P_Problem_class object.

        @param use_objective: determines whether the L_P_Objective is imported from
        the L_P_Other_Value problem

        For dictionaries the L_p_Constraints will be named with the keys
        For tuples an unique L_P_Name will be generated
        For LpProblems the L_P_Name of the problem will be added to the L_p_Constraints
        L_P_Name
        """
        if isinstance(L_P_Other_Value, dict):
            for L_P_Name in L_P_Other_Value:
                self.L_p_Constraints[L_P_Name] = L_P_Other_Value[L_P_Name]
        elif isinstance(L_P_Other_Value, L_P_Problem_class):
            for v in set(L_P_Other_Value.L_P_variables_List()).difference(self.L_P_variables_List()):
                v.L_P_Name = L_P_Other_Value.L_P_Name + v.L_P_Name
            for L_P_Name,c in L_P_Other_Value.L_p_Constraints.items():
                c.L_P_Name = L_P_Other_Value.L_P_Name + L_P_Name
                self.L_P_Constraint_ADD(c)
            if use_objective:
                self.L_P_Objective += L_P_Other_Value.L_P_Objective
        else:
            for c in L_P_Other_Value:
                if isinstance(c,tuple):
                    L_P_Name = c[0]
                    c = c[1]
                else:
                    L_P_Name = None
                if not L_P_Name: L_P_Name = c.L_P_Name
                if not L_P_Name: L_P_Name = self.Notused_Constraint()
                self.L_p_Constraints[L_P_Name] = c

    def Constraint_Coefficients(self, L_P_translate = None):
        coefs = []
        if L_P_translate == None:
            for c in self.L_p_Constraints:
                Constrs = self.L_p_Constraints[c]
                coefs.L_P_Extend_constraint([(v.L_P_Name, c, Constrs[v]) for v in Constrs])
        else:
            for c in self.L_p_Constraints:
                ctr = L_P_translate[c]
                Constrs = self.L_p_Constraints[c]
                coefs.L_P_Extend_constraint([(L_P_translate[v.L_P_Name], ctr, Constrs[v]) for v in Constrs])
        return coefs
