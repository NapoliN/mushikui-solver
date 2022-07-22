from statistics import mean, median, mode
from time import sleep
import request
import solver
from datetime import date, timedelta
import matplotlib.pyplot as plt

d1 = date(2022,6,1)
d2 = date(2022,7,31)
score = []
for i in range((d2-d1).days + 1):
    d = d1 + timedelta(i)
    print(d)
    eq_pos = request.get_precondition(d)
    print(f"equation pos idx = {eq_pos}")

    s = solver.Solver(eq_pos)
    clear = False
    #s.add_distinct_condition()
    for i in range(10):
        print(f"Searching answer {i} ",end="")
        op_cond = s.ope_choices()
        loop_flag = False
        # 演算子の組み合わせを全探索して成り立つ等式を探す
        for ops in op_cond:
            op1,op2 = ops[0],ops[1]
            #print(ops)
            #print(f"ops is {op1,op2}")
            # 可能ならば相異なる数字を選ぶ
            dis_flag = s.add_distinct_condition()
            # 等式制約
            s.add_operand_constraint(op1,op2)
            if s.check():
                s.createModel()
                s.pop(dis_flag)          
                expr = s.get_format_expression()
                print(expr,end=" ")

                fb = request.send_answer(expr,d)
                print("check=",end="")
                for c in fb:
                    print("🟩" if c == 2 else "🟨" if c == 1 else "⬜",end="")
                print("")
                
                # 正答
                if fb == [2,2,2,2,2,2]:
                    clear = True
                s.add_feedback_constraint(fb)
                loop_flag = True
                break
            # 条件を満たす等式が見つからなかった場合
            else:
                s.pop(dis_flag)

        # 相異なる数字を選んだ等式が作れなかった場合
        if not loop_flag:
            for ops in op_cond:
                op1,op2 = ops[0],ops[1]
                s.add_operand_constraint(op1,op2)
                if s.check():
                    s.createModel()
                    s.pop(False)            
                    expr = s.get_format_expression()
                    print(expr,end=" ")
                    fb = request.send_answer(expr,d)
                    print("check=",end="")
                    for c in fb:
                        print("🟩" if c == 2 else "🟨" if c == 1 else "⬜",end="")
                    print("")
                    if fb == [2,2,2,2,2,2]:
                        clear = True
                    s.add_feedback_constraint(fb)
                    loop_flag = True
                    break
                else:            
                    s.pop(False)
        if clear:
            print("Solve!")
            score.append(i+1)
            break
        sleep(1)

print(mean(score),median(score),mode(score))
plt.hist(score)
plt.show()