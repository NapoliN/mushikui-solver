import z3

TYPE_NUM = 0
TYPE_OPE = 1
TYPE_UND = 2
EQUATION_TYPE = (
    (TYPE_NUM,TYPE_NUM,TYPE_OPE,TYPE_NUM,TYPE_OPE,TYPE_NUM),
    (TYPE_NUM,TYPE_NUM,TYPE_NUM,TYPE_NUM,TYPE_OPE,TYPE_NUM),
    (TYPE_NUM,TYPE_OPE,TYPE_NUM,TYPE_NUM,TYPE_OPE,TYPE_NUM),
    (TYPE_NUM,TYPE_NUM,TYPE_OPE,TYPE_NUM,TYPE_NUM,TYPE_NUM),
    (TYPE_NUM,TYPE_OPE,TYPE_NUM,TYPE_OPE,TYPE_NUM,TYPE_NUM),
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
        self.type = type
        self.__number_symbol = z3.Int("hole" + str(idx))
        self.__operand_possibility = [COND_UNCHECK] * 4
        self.is_reveal = False
    
    @property
    def possiblity(self):
        return tuple(self.__operand_possibility)

    @property
    def symbol(self):
        return self.__number_symbol

    def is_variable(self):
        return self.type == TYPE_NUM
    
    def set_possibility(self,ope,cond):
        self.__operand_possibility[ope] = cond

    def __str__(self):
        if self.current_op == OPE_ADD:
            return "+"
        elif self.current_op == OPE_SUB:
            return "-"
        elif self.current_op == OPE_MUL:
            return "*"
        elif self.current_op == OPE_DIV:
            return "/"
        else:
            raise Exception("operand unset")

class Solver():
    def __init__(self,equal_position):
        self.__solver = z3.Solver()
        self.__equal_position = equal_position
        self.holes = [Hole(EQUATION_TYPE[equal_position][i],i) for i in range(6)]
        self.model: z3.ModelRef = None
        for h in self.holes:
            if h.is_variable():
                sv = h.symbol
                self.__solver.add(z3.And(0 <= sv, sv < 10))
        self.__solver.push()

    def check(self):
        return self.__solver.check() == z3.sat

    def get_format_expression(self):
        if self.model == None:
            raise Exception("Model is None")
        tmp = ""
        #print(self.model)
        for h in self.holes:
            if h.is_variable():
                tmp += str(self.model[h.symbol].as_long())
            else:
                tmp += str(h)
        return tmp[0:self.__equal_position+1] + "=" + tmp[self.__equal_position+1:]

    def createModel(self):
        self.model = self.__solver.model()

    def add_operand_constraint(self,ope1,ope2=None) -> None:
        st1 = None
        st2 = None
        num_idx = [i for i in range(6) if EQUATION_TYPE[self.__equal_position][i] == TYPE_NUM]
        ope_idx = [i for i in range(6) if EQUATION_TYPE[self.__equal_position][i] == TYPE_OPE]
        
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

        # a = b ? c ? d
        # a = bc ? de
        if self.__equal_position == 0:
            if ope2 == None:
                raise Exception("ope2 is need")
            a,b,c,d = [self.holes[i].symbol for i in num_idx]
            
            self.holes[ope_idx[0]].current_op = ope1
            self.holes[ope_idx[1]].current_op = ope2
            st1 = a
            # 計算順序が逆転する場合
            if (ope1 == OPE_ADD or ope1 == OPE_SUB) and (ope2 == OPE_MUL or ope2 == OPE_DIV):
                tmp = stmt_generator(c,d,ope2)
                st2 = stmt_generator(b,tmp,ope1)
                
            # 左から右に計算してよい場合
            else:
                tmp = stmt_generator(b,c,ope1)
                st2 = stmt_generator(tmp,d,ope2)

        # ab = cd ? e
        elif self.__equal_position == 1:
            a,b,c,d,e = [self.holes[i].symbol for i in num_idx]
            self.holes[ope_idx[0]].current_op = ope1
            a_deca = stmt_generator(a,10,OPE_MUL)
            st1 = stmt_generator(a_deca,b,OPE_ADD)

            c_deca = stmt_generator(c,10,OPE_MUL)
            cd = stmt_generator(c_deca,d,OPE_ADD)
            st2 = stmt_generator(cd,e,ope1)

        # a ? b = c ? d
        elif self.__equal_position == 2:
            if ope2 == None:
                raise Exception("ope2 is need")
            a,b,c,d = [self.holes[i].symbol for i in num_idx]
            self.holes[ope_idx[0]].current_op = ope1
            self.holes[ope_idx[1]].current_op = ope2
            st1 = stmt_generator(a,b,ope1)
            st2 = stmt_generator(c,d,ope2)

        # ab ? c = de
        # a ? bc = de
        elif self.__equal_position == 3:
            a,b,c,d,e = [self.holes[i].symbol for i in num_idx]
            self.holes[ope_idx[0]].current_op = ope1
            a_deca = stmt_generator(a,10,OPE_MUL)
            ab = stmt_generator(a_deca,b,OPE_ADD)
            st1 = stmt_generator(ab,c,ope1)

            d_deca = stmt_generator(d,10,OPE_MUL)
            st2 = stmt_generator(d_deca,e,OPE_ADD)

        # a ? b ? c = d
        # ab ? cd = e
        elif self.__equal_position == 4:
            if ope2 == None:
                raise Exception("ope2 is need")
            a,b,c,d = [self.holes[i].symbol for i in num_idx]
            self.holes[ope_idx[0]].current_op = ope1
            self.holes[ope_idx[1]].current_op = ope2
            # 計算順序が逆転する場合
            if (ope1 == OPE_ADD or ope1 == OPE_SUB) and (ope2 == OPE_MUL or ope2 == OPE_DIV):
                tmp = stmt_generator(b,c,ope2)
                st1 = stmt_generator(a,tmp,ope1)
            # 左から右に計算してよい場合
            else:
                tmp = stmt_generator(a,b,ope1)
                st1 = stmt_generator(tmp,c,ope2)
            st2 = d

        assert(st1 != None and st2 != None)
        #print(st1,st2)
        self.__solver.add(st1 == st2)
        self.__solver.push()
    
    def add_feedback_constraint(self,check_arr):
        if self.model == None:
            raise Exception("Model is None")
        num_idx = [i for i in range(6) if EQUATION_TYPE[self.__equal_position][i] == TYPE_NUM]
        ope_idx = [i for i in range(6) if EQUATION_TYPE[self.__equal_position][i] == TYPE_OPE]
        for i in num_idx:
            hole = self.holes[i]
            check = check_arr[i]
            if check == 2:
                hole.is_reveal = True
                self.__solver.add(hole.symbol == self.model[hole.symbol])
            elif check == 1:
                or_ref = []
                for h in self.holes:
                    if h.is_variable():
                        v = self.model[hole.symbol]
                        if h == hole:
                            self.__solver.add(z3.Not(h.symbol == v))
                        else:
                            or_ref.append(h.symbol == v)
                self.__solver.add(z3.Or(*or_ref))
                
            else:
                self.__solver.add(z3.Not(hole.symbol == self.model[hole.symbol]))

        for i in ope_idx:
            hole = self.holes[i]
            check = check_arr[i]
            num = 0 if i < 3 else 1
            if check == 2:
                hole.set_possibility(hole.current_op,COND_USE)
            elif check == 1:
                hole.set_possibility(hole.current_op,COND_UNUSE)
                if(len(ope_idx) > 1):
                    rev_i = ope_idx[0] if i == ope_idx[1] else ope_idx[1]
                    rev_hole = self.holes[rev_i]
                    rev_hole.set_possibility(hole.current_op,COND_USE)
            else:
                hole.set_possibility(hole.current_op,COND_UNUSE)
                if(len(ope_idx) > 1):
                    rev_i = ope_idx[0] if i == ope_idx[1] else ope_idx[1]
                    rev_hole = self.holes[rev_i]
                    rev_hole.set_possibility(hole.current_op,COND_UNUSE)

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

    def ope_choices(self,num):
        ope_idx = [i for i in range(6) if EQUATION_TYPE[self.__equal_position][i] == TYPE_OPE]
        if len(ope_idx) == 1 and num == 1:
            return [None]

        arr = self.holes[ope_idx[num]].possiblity
        if COND_USE in arr:
            return [arr.index(COND_USE)]
        else:
            return [i for i in range(4) if arr[i] == COND_UNCHECK]
