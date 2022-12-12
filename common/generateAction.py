import random
import numpy as np

from Formula import Formula
from Sequent import Sequent
import displaySequent

sequent_maxLen = 8 #シーケントの両辺の論理式の上限
fml_maxLen = 8 #各論理式に出現する命題変数の総数の上限

AP=['A', 'B', 'C'] #命題変数のリスト

unInf = ['Emp', 'LW', 'RW', 'L&', 'R|', 'R->', 'L!', 'R!'] #1引数の推論規則, Empは恒等action
binInf = ['R&', 'L|', 'L->'] #2引数の推論規則

def generateState(ls): #ls=[親シーケント, 推論規則, 引数1, 引数2] を受け取って子のシーケントを生成, 適用できない場合はFalseを返す
    left_seq = ls[0].left
    right_seq = ls[0].right
    if ls[1] == 'Emp':
        return ls[0]
    elif ls[1] == 'LW':
        left_seq.add(Formula(ls[2]))
        return Sequent(left_seq, right_seq)
    elif ls[1] == 'RW':
        right_seq.add(Formula(ls[2]))
        return Sequent(left_seq, right_seq)

    elif ls[1] == 'L&':
        if (Formula(ls[2]) in left_seq)&(Formula(ls[3]) in left_seq):
            conc = '(' + ls[2] + ')&(' + ls[3] + ')'
            left_seq.add(Formula(conc))
            left_seq.remove(Formula(ls[2]))
            left_seq.remove(Formula(ls[3]))
            return Sequent(left_seq, right_seq)
        else:
            return False

    elif ls[1] == 'R|':
        if (Formula(ls[2]) in right_seq)&(Formula(ls[3]) in right_seq):
            conc = '(' + ls[2] + ')|(' + ls[3] + ')'
            right_seq.add(Formula(conc))
            right_seq.remove(Formula(ls[2]))
            right_seq.remove(Formula(ls[3]))
            return Sequent(left_seq, right_seq)
        else:
            return False

    elif ls[1] == 'R->':
        if (Formula(ls[2]) in left_seq)&(Formula(ls[3]) in right_seq):
            conc = '(' + ls[2] + ')->(' + ls[3] + ')'
            right_seq.add(Formula(conc))
            left_seq.remove(Formula(ls[2]))
            right_seq.remove(Formula(ls[3]))
            return Sequent(left_seq, right_seq)
        else:
            return False

    elif ls[1] == 'L!':
        if Formula(ls[2]) in right_seq:
            conc = '!(' + ls[2] + ')'
            left_seq.add(Formula(conc))
            right_seq.remove(Formula(ls[2]))
            return Sequent(left_seq, right_seq)
        else:
            return False

    elif ls[1] == 'R!':
        if Formula(ls[2]) in left_seq:
            conc = '!(' + ls[2] + ')'
            right_seq.add(Formula(conc))
            left_seq.remove(Formula(ls[2]))
            return Sequent(left_seq, right_seq)
        else:
            return False

def randomAction(state):
    soundness = False #ランダムに選んだ規則を適用できるか？

    actionInf = 'Emp'
    argFml1 = ''
    argFml2 = ''

    while soundness == False:
        actionInf = random.choice(unInf)
        if actionInf == 'Emp':
            soundness = True
            argFml1 = ''
            argFml2 = ''

        elif actionInf in ['LW','RW']:
            soundness = True
            argFml1 = random.choice(AP)
            argFml2 = ''

        elif actionInf == 'L&':
            if len(state.left) >= 2:
                soundness = True
                args = random.sample(list(state.left), 2)
                argFml1 = args[0].string_formula
                argFml2 = args[1].string_formula

        elif actionInf == 'R|':
            if len(state.right) >= 2:
                soundness = True
                args = random.sample(list(state.right), 2)
                argFml1 = args[0].string_formula
                argFml2 = args[1].string_formula

        elif actionInf == 'R->':
            if len(state.left) >= 1 & len(state.right) >= 1:
                soundness = True
                argFml1 = random.choice(list(state.left)).string_formula
                argFml2 = random.choice(list(state.right)).string_formula

        elif actionInf == 'L!':
            if len(state.right) >= 1:
                soundness = True
                argFml1 = random.choice(list(state.right)).string_formula

        elif actionInf == 'R!':
            if len(state.left) >= 1:
                soundness = True
                argFml1 = random.choice(list(state.left)).string_formula

    return [actionInf, argFml1, argFml2]


def checkLength(state): #長さの上限チェック
    if len(state.left)+len(state.left) > sequent_maxLen:
        return False
    else:
        for i in list(state.left)+list(state.left):
            ap_num = 0
            for ap in AP:
                ap_num+=i.string_formula.count(ap)
            if ap_num > fml_maxLen:
                return False
    return True


def generateUnAction (state, actionList, actionProbs):
  #actionList→stateに対して、過去に選択されたactionのList
  #actionProbs→actionList内のactionを選択する確率+ランダムにactionを生成する確率
  #例：actionList = [action1, action2, action3]のとき、
  #actionProbs = [0.7, 0.1, 0.1, 0.1]
  #つまり、len(actionProbs) = len(actionList) + 1

  #以下は関数の処理です
  #randomActionはランダムに取得したaction(昨日作っていただいたやつ)
  #generateStateはstateとactionからnext_stateを導く関数

  while True: #適用できなければやり直す
      actionList.append(randomAction(state)) #末尾のアクションを抽選
      actionNum = np.random.choice(len(actionList), p=actionProbs)
      action=actionList[actionNum]
      next_state = generateState([state]+action)
      if next_state != False: #適用できるかチェック
          if checkLength(next_state): #長さのチェック
              break #問題がなければ終了
      actionList.pop(-1) #再度末尾のアクションを抽選するため, 一度消す
  return [next_state, action]


#以下動作テスト

seq1=Sequent({Formula("C"),Formula("B")},{Formula("!(A)")})

print(displaySequent.displaySeq(seq1))

result = generateUnAction(seq1,[['L!','!(B)',''], ['R!','A','']],[0.2, 0.3, 0.5])
print(result[1])
print(displaySequent.displaySeq(result[0]))
