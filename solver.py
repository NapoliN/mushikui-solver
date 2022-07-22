from ast import stmt
from itertools import product
from math import prod
import z3

TYPE_NUM = 0
TYPE_OPE = 1
TYPE_UND = 2
EQUATION_TYPE = (
    (TYPE_NUM,TYPE_NUM,TYPE_UND,TYPE_UND,TYPE_UND,TYPE_NUM),
    (TYPE_NUM,TYPE_NUM,TYPE_NUM,TYPE_UND,TYPE_UND,TYPE_NUM),
    (TYPE_NUM,TYPE_OPE,TYPE_NUM,TYPE_NUM,TYPE_OPE,TYPE_NUM),
    (TYPE_NUM,TYPE_UND,TYPE_UND,TYPE_NUM,TYPE_NUM,TYPE_NUM),
    (TYPE_NUM,TYPE_UND,TYPE_UND,TYPE_UND,TYPE_NUM,TYPE_NUM),
)

EQ0_PATTERN = (
    (TYPE_NUM, TYPE_NUM,TYPE_OPE,TYPE_NUM,TYPE_OPE,TYPE_NUM),
    (TYPE_NUM, TYPE_NUM,TYPE_NUM,TYPE_OPE,TYPE_NUM,TYPE_NUM)
)

EQ1_PATTERN = (
    (TYPE_NUM,TYPE_NUM,TYPE_NUM,TYPE_NUM,TYPE_OPE,TYPE_NUM),
    (TYPE_NUM,TYPE_NUM,TYPE_NUM,TYPE_OPE,TYPE_NUM,TYPE_NUM),
)

EQ3_PATTERN = (
    (TYPE_NUM,TYPE_NUM,TYPE_OPE,TYPE_NUM,TYPE_NUM,TYPE_NUM),
    (TYPE_NUM,TYPE_OPE,TYPE_NUM,TYPE_NUM,TYPE_NUM,TYPE_NUM)
)

EQ4_PATTERN = (
    (TYPE_NUM,TYPE_OPE,TYPE_NUM,TYPE_OPE,TYPE_NUM,TYPE_NUM),
    (TYPE_NUM,TYPE_NUM,TYPE_OPE,TYPE_NUM,TYPE_NUM,TYPE_NUM),
)

OPE_ADD = 0
OPE_SUB = 1
OPE_MUL = 2
OPE_DIV = 3

COND_UNCHECK = 0
COND_USE = 1
COND_UNUSE = 2

class Hole():
    def __init__(self,type,idx):
        self.condition = type
        self.current_type = type
        self.__current_op = None
        self.__number_symbol = z3.Int("hole" + str(idx))
        self.__operand_possibility = [COND_UNCHECK] * 4
        self.is_reveal = False
    
    @property
    def possiblity(self):
        return self.__operand_possibility

    @property
    def symbol(self):
        return self.__number_symbol

    @property
    def current_op(self):
        return self.__current_op

    @current_op.setter
    def current_op(self,type):
        self.__current_op = type

    def is_variable(self):
        return self.condition == TYPE_NUM

    def is_undefined(self):
        return self.condition == TYPE_UND
    
    def set_possibility(self,ope,cond):
        self.__operand_possibility[ope] = cond

    def __str__(self):
        assert(self.current_type == TYPE_OPE)
        if self.__current_op == OPE_ADD:
            return "+"
        elif self.__current_op == OPE_SUB:
            return "-"
        elif self.__current_op == OPE_MUL:
            return "*"
        elif self.__current_op == OPE_DIV:
            return "/"
        else:
            raise Exception("operand unset")

class Solver():
    def __init__(self,equal_position):
        self.__solver = z3.Solver()
        self.__equal_position = equal_position
        self.holes = [Hole(EQUATION_TYPE[equal_position][i],i) for i in range(6)]
        self.model: z3.ModelRef = None
        self.yellow_constraint = []
        for h in self.holes:
            if h.condition != TYPE_OPE:
                sv = h.symbol
                self.__solver.add(z3.And(0 <= sv, sv < 10))
        self.__solver.push()

    def check(self):
        ret = self.__solver.check() == z3.sat
        #if not ret:
        #    print(self.__solver)
        return ret

    def get_format_expression(self):
        if self.model == None:
            raise Exception("Model is None")
        tmp = ""
        #print(self.model)
        for h in self.holes:
            if h.current_type == TYPE_NUM:
                tmp += str(self.model[h.symbol].as_long())
            else:
                tmp += str(h)
        return tmp[0:self.__equal_position+1] + "=" + tmp[self.__equal_position+1:]

    def createModel(self):
        self.model = self.__solver.model()

    def add_operand_constraint(self,ope1,ope2=None) -> None:
        st1 = None
        st2 = None
        
        # statement2個とoperandから新たなstatementを生成
        def stmt_generator(stmt1,stmt2,operand_type):
            stmt = None
            if operand_type == OPE_ADD:
                stmt = stmt1 + stmt2
            elif operand_type == OPE_SUB:
                stmt = stmt1 - stmt2
            elif operand_type == OPE_MUL:
                stmt = stmt1 * stmt2
            else:
                stmt = stmt1 / stmt2
                self.__solver.add(z3.And(stmt2 > 0, stmt1%stmt2==0))
            assert(stmt != None)
            return stmt
        
        def make2digit(sym1,sym2):
            self.__solver.add(z3.Not(sym1 == 0))
            sym1_deca = stmt_generator(sym1,10,OPE_MUL)
            return stmt_generator(sym1_deca,sym2,OPE_ADD)

        # a = b ? c ? d
        # a = bc ? de
        if self.__equal_position == 0:
            # a = bc ? de
            if ope2 == None:
                a,b,c,d,e = [self.holes[i].symbol for i in [0,1,2,4,5]]
                for i in range(6):
                    self.holes[i].current_type = EQ0_PATTERN[1][i]
                self.holes[3].current_op = ope1
                st1 = a
                bc = make2digit(b,c)
                de = make2digit(d,e)
                st2 = stmt_generator(bc,de,ope1)

                for n in self.yellow_constraint:
                    self.__solver.add(z3.Not(self.holes[3].symbol == n))

            # a = b ? c ? d
            else:
                a,b,c,d = [self.holes[i].symbol for i in [0,1,3,5]]
                for i in range(6):
                    self.holes[i].current_type = EQ0_PATTERN[0][i]
                
                self.holes[2].current_op = ope1
                self.holes[4].current_op = ope2
                st1 = a
                # 計算順序が逆転する場合
                if (ope1 == OPE_ADD or ope1 == OPE_SUB) and (ope2 == OPE_MUL or ope2 == OPE_DIV):
                    tmp = stmt_generator(c,d,ope2)
                    st2 = stmt_generator(b,tmp,ope1)
                    
                # 左から右に計算してよい場合
                else:
                    tmp = stmt_generator(b,c,ope1)
                    st2 = stmt_generator(tmp,d,ope2)
                
                for n in self.yellow_constraint:
                    self.__solver.add(z3.Not(self.holes[2].symbol == n))
                    self.__solver.add(z3.Not(self.holes[4].symbol == n))

        # ab = cd ? e
        # ab = c ? de
        elif self.__equal_position == 1:
            #ab = cd ? e
            if ope2 == None:
                for i in range(6):
                    self.holes[i].current_type = EQ1_PATTERN[0][i]
                a,b,c,d,e = [self.holes[i].symbol for i in [0,1,2,3,5]]
                self.holes[4].current_op = ope1
                st1 = make2digit(a,b)

                cd = make2digit(c,d)
                st2 = stmt_generator(cd,e,ope1)
                for n in self.yellow_constraint:
                    self.__solver.add(z3.Not(self.holes[4].symbol == n))
            #ab = c ? de
            else:
                for i in range(6):
                    self.holes[i].current_type = EQ1_PATTERN[1][i]
                a,b,c,d,e = [self.holes[i].symbol for i in [0,1,2,4,5]]
                self.holes[3].current_op = ope2
                st1 = make2digit(a,b)
                de = make2digit(d,e)
                st2 = stmt_generator(c,de,ope2)
                for n in self.yellow_constraint:
                    self.__solver.add(z3.Not(self.holes[3].symbol == n))

        # a ? b = c ? d
        elif self.__equal_position == 2:
            if ope2 == None:
                raise Exception("ope2 is need")
            a,b,c,d = [self.holes[i].symbol for i in [0,2,3,5]]
            self.holes[1].current_op = ope1
            self.holes[4].current_op = ope2
            st1 = stmt_generator(a,b,ope1)
            st2 = stmt_generator(c,d,ope2)
            for n in self.yellow_constraint:
                self.__solver.add(z3.Not(self.holes[1].symbol == n))
                self.__solver.add(z3.Not(self.holes[4].symbol == n))

        # ab ? c = de
        # a ? bc = de
        elif self.__equal_position == 3:
            #print(f"ope2 == None is {ope2==None}",end=" ")
            if ope2 == None:
                a,b,c,d,e = [self.holes[i].symbol for i in [0,1,3,4,5]]
                for i in range(6):
                    self.holes[i].current_type = EQ3_PATTERN[0][i]
                self.holes[2].current_op = ope1
                ab = make2digit(a,b)
                st1 = stmt_generator(ab,c,ope1)
                st2 = make2digit(d,e)
                for n in self.yellow_constraint:
                    self.__solver.add(z3.Not(self.holes[2].symbol == n))
            else:
                a,b,c,d,e = [self.holes[i].symbol for i in [0,2,3,4,5]]
                for i in range(6):
                    self.holes[i].current_type = EQ3_PATTERN[1][i]
                self.holes[1].current_op = ope2
                bc = make2digit(b,c)
                st1 = stmt_generator(a,bc,ope2)
                st2 = make2digit(d,e)
                for n in self.yellow_constraint:
                    self.__solver.add(z3.Not(self.holes[1].symbol == n))

        # a ? b ? c = d
        # ab ? cd = e
        elif self.__equal_position == 4:
            if ope2 == None:
                for i in range(6):
                    self.holes[i].current_type = EQ4_PATTERN[1][i]
                a,b,c,d,e = [self.holes[i].symbol for i in [0,1,3,4,5]]
                self.holes[2].current_op = ope1
                ab = make2digit(a,b)
                cd = make2digit(c,d)
                st1 = stmt_generator(ab,cd,ope1)
                st2 = e
                for n in self.yellow_constraint:
                    self.__solver.add(z3.Not(self.holes[2].symbol == n))
                    
            else:
                for i in range(6):
                    self.holes[i].current_type = EQ4_PATTERN[0][i]
                a,b,c,d = [self.holes[i].symbol for i in [0,2,4,5]]
                self.holes[1].current_op = ope1
                self.holes[3].current_op = ope2
                # 計算順序が逆転する場合
                if (ope1 == OPE_ADD or ope1 == OPE_SUB) and (ope2 == OPE_MUL or ope2 == OPE_DIV):
                    tmp = stmt_generator(b,c,ope2)
                    st1 = stmt_generator(a,tmp,ope1)
                # 左から右に計算してよい場合
                else:
                    tmp = stmt_generator(a,b,ope1)
                    st1 = stmt_generator(tmp,c,ope2)
                st2 = d
                for n in self.yellow_constraint:
                    self.__solver.add(z3.Not(self.holes[1].symbol == n))
                    self.__solver.add(z3.Not(self.holes[3].symbol == n))

        assert(st1 != None and st2 != None)
        self.__solver.add(st1 == st2)
        self.__solver.push()
    
    def add_feedback_constraint(self,check_arr):
        if self.model == None:
            raise Exception("Model is None")
        for i in range(6):
            hole = self.holes[i]
            check = check_arr[i]
            # 今回の等式で数字として用いられているHole
            if hole.current_type == TYPE_NUM:
                # Green
                if check == 2:
                    hole.is_reveal = True
                    hole.condition = TYPE_NUM
                    self.__solver.add(hole.symbol == self.model[hole.symbol])
                # Yellow
                elif check == 1:
                    v = self.model[hole.symbol]
                    self.yellow_constraint.append(v)
                    or_ref = []
                    for h in self.holes:
                        if h.current_type == TYPE_NUM:
                            if h == hole:
                                self.__solver.add(z3.Not(h.symbol == v))
                            else:
                                or_ref.append(h.symbol == v)
                        # FIXME?
                        else:
                            or_ref.append(h.symbol == v)
                    self.__solver.add(z3.Or(*or_ref))
                # Gray
                else:
                    self.__solver.add(z3.Not(hole.symbol == self.model[hole.symbol]))
            
            elif hole.current_type == TYPE_OPE:
                # Green
                if check == 2:
                    hole.set_possibility(hole.current_op,COND_USE)
                    for h in self.holes:
                        h.condition = h.current_type                        
                # Yellow
                # FIXME 難しい
                elif check == 1:
                    hole.set_possibility(hole.current_op,COND_UNUSE)
                    #if(len(ope_idx) > 1):
                    #    rev_i = ope_idx[0] if i == ope_idx[1] else ope_idx[1]
                    #    rev_hole = self.holes[rev_i]
                    #    rev_hole.set_possibility(hole.current_op,COND_USE)
                # Gray
                else:
                    for h in self.holes:
                        h.set_possibility(hole.current_op,COND_UNUSE)

        self.__solver.push()

    def add_distinct_condition(self):
        t = []
        for h in self.holes:
            if h.is_variable() and not h.is_reveal:
                t.append(h.symbol)
        if len(t) > 0:
            self.__solver.add(z3.Distinct(*t))
            self.__solver.push()
            return True
        return False

    def pop(self,dis_flag):
        self.__solver.pop(2)
        if dis_flag:
            self.__solver.pop()
        self.__solver.push()

    def ope_choices(self):
        def extract(arr):
            return [arr.index(COND_USE)] if COND_USE in arr else [i for i in range(4) if arr[i] == COND_UNCHECK]

        ret = []
        # a = b ? c ? d
        # a = bc ? de
        if self.__equal_position == 0:
            if self.holes[2].condition == TYPE_OPE or self.holes[2].condition == TYPE_UND:
                tmp = extract(self.holes[2].possiblity)
                tmp2 = extract(self.holes[4].possiblity)
                ret.extend(product(tmp,reversed(tmp2)))
            if self.holes[3].condition == TYPE_OPE or self.holes[3].condition == TYPE_UND:
                tmp = extract(self.holes[3].possiblity)
                ret.extend(product(tmp,[None]))
        # ab = cd ? e
        # ab = c ? de
        elif self.__equal_position == 1:
            tmp = extract(self.holes[4].possiblity)
            ret.extend(product(tmp,[None]))
            tmp2 = extract(self.holes[3].possiblity)
            ret.extend(product([None],tmp2))
        # a ? b = c ? d
        elif self.__equal_position == 2:
            tmp = extract(self.holes[1].possiblity)
            tmp2 = extract(self.holes[4].possiblity)
            ret.extend(product(tmp,tmp2))
        # ab ? c = de
        # a ? bc = de
        elif self.__equal_position == 3:
            tmp = extract(self.holes[2].possiblity)
            ret.extend(product(tmp,[None]))
            tmp2 = extract(self.holes[1].possiblity)
            ret.extend(product([None],tmp2))
        # a ? b ? c = d
        # ab ? cd = e
        elif self.__equal_position == 4:
            if self.holes[1].condition == TYPE_OPE or self.holes[1].condition == TYPE_UND:
                tmp = extract(self.holes[1].possiblity)
                tmp2 = extract(self.holes[3].possiblity)
                ret.extend(product(tmp,reversed(tmp2)))
            if self.holes[2].condition == TYPE_OPE or self.holes[2].condition == TYPE_UND:
                tmp = extract(self.holes[2].possiblity)
                ret.extend(product(tmp,[None]))
        return ret
