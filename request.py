import requests
from datetime import datetime


API_URL = "https://api.mushikui.trasta.dev/expression/"

#OPE_ADD = 11
#OPE_SUB = 12
#OPE_MUL = 13
#OPE_DIV = 14
#OPE_EQ = 15

def get_precondition(date:datetime=datetime.now()):
    res = requests.get(API_URL+date.strftime("%Y%m%d"))
    json_data = res.json()
    return json_data["pos"] - 1

def send_answer(expr,date:datetime=datetime.now()):
    send_data = {"expression" : expr}
    res = requests.post(API_URL+date.strftime("%Y%m%d"),json=send_data)
    #print(res.json())
    return res.json()["check"]