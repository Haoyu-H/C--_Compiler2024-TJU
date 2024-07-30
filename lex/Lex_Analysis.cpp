#include <iostream>
#include <fstream>
#include <sstream>
#include <iomanip>
#include <set>
#include <map>
#include <vector>
#include <algorithm>
#include <math.h>
#include <queue>
#include <stack>
#include <stdlib.h>

using namespace std;
#define NFA_SIZE 30

typedef struct trans_map{
    char rec;
    int now;
    int next;
} transform_map;

typedef struct finite_automata{
    vector<char> input_symbols;       //可以输入的字符集
    set<int> states;                  //状态集合  
    map<int, string> state_labels;    //非终态的label是描述，终态的label是输出
    set<transform_map> trans_map;     //子集映射规则
    set<int> start;                   //初始集
    set<int> final;                   //终态集
} FA;

map<string, string> symbols_table = {
    {"int","KW"},{"void","KW"},{"return","KW"},{"const","KW"},{"main","KW"},{"float","KW"},{"if","KW"},{"else","KW"},
    {"+","OP"},{"-","OP"},{"*","OP"},{"/","OP"},{"%","OP"},{"=","OP"},{">","OP"},
    {"<","OP"},{"==","OP"},{"<=","OP"},{">=","OP"},{"!=","OP"},{"&&","OP"},{"||","OP"},
    {"(","SE"},{")","SE"},{"{","SE"},{"}","SE"},{";","SE"},{",","SE"}
};
map<string, string> processed_symbols_table = {};

vector<char> lex_input_symbols = {'n','l','o','s','_','0','=','>','<','!','&','|','-','.'};
set<int> lex_states = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20};
map<int,string> lex_state_labels = {{1,"n"},{2,"l"},{3,"o"},{4,"s"},{5,"_"},{7,"="},{8,">"},{9,"<"},{10,"!"},{11,"&"},{12,"|"},{13,"INT"},
{14,"SE"},{15,"I&K"},{16,"OP"},{17,"none"},{18,"OP"},{20,"FLOAT"}}; 
set<int> lex_start = {17};
set<int> lex_final = {13,14,15,16,18,20};
set<transform_map> lex_trans_map = {{'@',1,13},{'n',13,13},{'@',2,15},{'l',15,15},{'_',15,15},{'n',15,15},{'@',4,14},{'@',3,16},
{'@',5,15},{'@',7,16},{'@',8,16},{'=',7,16},{'=',8,16},{'@',9,16},{'=',9,16},{'=',10,16},{'&',11,16},{'|',12,16},{'n',18,13},{'n',17,1},{'l',17,2},{'o',17,3},{'s',17,4},
{'_',17,5},{'=',17,7},{'>',17,8},{'<',17,9},{'!',17,10},{'&',17,11},{'|',17,12},{'-',17,18},{'.',13,20},{'@',20,20},{'n',20,20}};


bool operator<(const trans_map &a,const trans_map &b){
    return a.now + 100*int(a.rec) < b.now + 100*int(b.rec);
}



set<int> getClosure(const set<int>& current_states, const FA& NFA) {
    set<int> closure = current_states; // 初始化闭包为当前状态集
    set<int> worklist = current_states; // 工作列表，用于存储待处理的状态

    // 只要工作列表不为空，就继续处理
    while (!worklist.empty()) {
        // 取出并移除工作列表中的一个状态
        int state = *worklist.begin();
        worklist.erase(worklist.begin());

        // 遍历NFA的所有转换
        for (const auto& tm : NFA.trans_map) {
            // 如果转换是ε转换，并且当前状态匹配，且新状态不在闭包中
            if (tm.rec == '@' && state == tm.now && closure.insert(tm.next).second) {
                worklist.insert(tm.next); // 将新状态加入工作列表
            }
        }
    }

    return closure; // 返回闭包
}


set<int> getNextState(set<int> current_states, char input, FA NFA){
    set<int> extended_states;
    for(set<int>::iterator i = current_states.begin();i != current_states.end();i++){
        int state = *i;
        trans_map trans;
        for(set<trans_map>::iterator j = NFA.trans_map.begin();j != NFA.trans_map.end();j++){
            trans = *j;
            if(trans.now == state && trans.rec == input){
                extended_states.insert(trans.next);
            }
        }
    }
    return getClosure(extended_states, NFA);
}

FA NFAdeterminization(FA NFA) {
    FA DFA;
    queue<set<int>> processing_set;
    map<set<int>, int> state_to_id; // 映射每个状态集合到一个唯一的ID
    int next_id = 1; // 下一个可用的状态ID

    // 初始化DFA
    DFA.input_symbols = NFA.input_symbols; // DFA的输入符号与NFA相同
    DFA.start = {1}; // 设置DFA的起始状态为1
    DFA.states.insert(1); // 将状态1添加到DFA的状态集合中
    // 获取NFA起始状态的闭包，并将其映射到DFA的起始状态
    state_to_id[getClosure(NFA.start, NFA)] = 1;
    // 将NFA起始状态的闭包加入待处理队列
    processing_set.push(getClosure(NFA.start, NFA));

    // 当还有待处理的状态时，循环继续
    while (!processing_set.empty()) {
        set<int> current_states = processing_set.front(); // 获取当前处理的状态集合
        processing_set.pop(); // 从队列中移除该状态集合
        int current_id = state_to_id[current_states]; // 获取当前状态集合对应的DFA状态ID

        // 遍历所有输入符号
        for (char ch : NFA.input_symbols) {
            // 获取在输入符号ch下的下一个状态集合
            set<int> next_states = getNextState(current_states, ch, NFA);
            if (next_states.empty()) continue; // 如果下一个状态集合为空，则跳过

            // 如果下一个状态集合还没有映射到DFA的状态ID
            if (!state_to_id.count(next_states)) {
                state_to_id[next_states] = ++next_id; // 映射到新的状态ID
                DFA.states.insert(next_id); // 将新状态ID添加到DFA的状态集合中
                processing_set.push(next_states); // 将新状态集合加入待处理队列

                // 检查新状态集合中是否包含NFA的终态
                for (int state : next_states) {
                    if (NFA.final.count(state)) {
                        DFA.final.insert(next_id); // 如果包含，则将对应的DFA状态标记为终态
                        DFA.state_labels[next_id] = NFA.state_labels[state]; // 并设置终态的标签
                        break; // 只需找到一个终态即可
                    }
                }
            }
            DFA.trans_map.insert({ch, current_id, state_to_id[next_states]});
        }
    }

    return DFA; // 返回构建好的DFA
}

FA minimize(FA DFA) {
    FA minDFA; // 创建一个新的FA对象，用于存储最小化后的DFA

    // 将输入符号从原始DFA复制到新的minDFA
    minDFA.input_symbols = DFA.input_symbols;

    map<int, int> state_mapping; // 创建一个映射，用于记录状态之间的对应关系
    set<int> non_final_states, final_states_by_label; // 创建两个集合，分别存储非终态和终态

    // 遍历DFA的所有状态，将它们分为终态和非终态
    for (int state : DFA.states) {
        if (DFA.final.count(state)) {
            final_states_by_label.insert(state);
        } else {
            non_final_states.insert(state);
        }
    }

    // 初始化状态映射，为每个状态分配一个新的ID
    int new_state_id = 0;
    for (int state : non_final_states) {
        state_mapping[state] = new_state_id++;
    }
    for (int state : final_states_by_label) {
        state_mapping[state] = new_state_id++;
    }

    // 根据状态映射，构建新的状态集合
    for (auto &mapping : state_mapping) {
        minDFA.states.insert(mapping.second);
        // 如果原始DFA的起始状态在映射中，将其添加到新的minDFA的起始状态
        if (DFA.start.count(mapping.first)) {
            minDFA.start.insert(mapping.second);
        }
        // 如果原始DFA的终态在映射中，将其添加到新的minDFA的终态，并复制标签
        if (DFA.final.count(mapping.first)) {
            minDFA.final.insert(mapping.second);
            minDFA.state_labels[mapping.second] = DFA.state_labels[mapping.first];
        }
    }

    // 构建转换规则，根据状态映射更新转换关系
    for (auto &trans : DFA.trans_map) {
        int new_now = state_mapping[trans.now];
        int new_next = state_mapping[trans.next];
        char rec = trans.rec;
        // 将新的转换关系添加到minDFA的转换映射中
        minDFA.trans_map.insert({rec, new_now, new_next});
    }

    return minDFA;
}





int GetBC(char ch){
    if(ch == ' ' || ch == '\t'){
        return 0;
    }
    return 1;
}

char GetCharType(char ch , char next_ch){
    if(ch >= '0' && ch <= '9')  return 'n';
    if(ch=='.') return '.';
    //if(ch == '0')  return '0';
    if((ch >= 'A' && ch <= 'Z')||(ch >= 'a' && ch <= 'z'))  return 'l';
    if(ch == '+' || ch == '-' || ch == '*' || ch == '/' || ch == '%')  return 'o';
    if(ch == '(' || ch == ')' || ch == '{' || ch == '}' || ch == ';' || ch == ',')  return 's';
    if(ch == '.' && (next_ch < '0' || next_ch > '9')){
        cout<< "浮点数输入错误，请在 . 后面加上数字"<<endl;
        exit(EXIT_FAILURE);
    }
    return ch;
}

void Generate_symbol_table(int state, string strToken, FA DFA){
    if((DFA.state_labels[state]=="INT" || DFA.state_labels[state]=="SE" || DFA.state_labels[state] == "OP") && !processed_symbols_table.count(strToken)){
        processed_symbols_table.insert({strToken,DFA.state_labels[state]});
    }
    else if(DFA.state_labels[state] == "I&K" && symbols_table[strToken] == "KW" && !processed_symbols_table.count("KW")){
        processed_symbols_table.insert({strToken,DFA.state_labels[state]});
    }
    else if(!processed_symbols_table.count(strToken)) processed_symbols_table.insert({strToken,"IDN"});
}

string Get_Tokens(int state, string strToken, FA DFA){
    if(DFA.state_labels[state]=="INT"){
        string s = "<INT,";
        string e = ">";
        s += strToken;
        s += e;
        return s;
    }
    if(DFA.state_labels[state]=="FLOAT"){
        string s = "<FLOAT,";
        string e = ">";
        s += strToken;
        s += e;
        return s;
    }  
    if(DFA.state_labels[state] == "SE"){
        string s = "<SE,";
        string e = ">";
        s += to_string(state);
        s += e;
        return s;
    }
    if(DFA.state_labels[state] == "OP"){
        string s = "<OP,";
        string e = ">";
        s += to_string(state);
        s += e;
        return s;
    }
    if(DFA.state_labels[state] == "I&K" && symbols_table[strToken] == "KW"){
        string s = "<KW,";
        string e = ">";
        s += to_string(state);
        s += e;
        return s;
    }
    string s = "<IDN,";
    string e = ">";
    s += strToken;
    s += e;
    return s;
}

void lexcial(const char* address, FA DFA , string x){
    fstream Test_sample(address);
    ofstream record_tokens;
    string lex ="../syntax/lex/lex";
    string txt =".txt";
    lex += x;
    lex += txt; 
    record_tokens.open(lex, ios::out | ios::trunc);
    if(Test_sample.is_open() && record_tokens.is_open()){ //先判断文件是否正确打开
        char ch;    //字符变量，存储最新读入的源程序字符
        string buf; //缓冲区
        while (getline(Test_sample,buf)){ //不断读入数据到缓冲区
            int current_state = *DFA.start.begin();
            string strToken = "";
            for( int i=0; i < buf.length() ; i++ ){ //遍历缓冲区的每一个元素
                ch = buf[i];
                while (!GetBC(ch)){ 
                    i++;
                    ch=buf[i];
                }
                char ch_type = GetCharType(ch, buf[i+1]);
                transform_map State_Transfer;
                for(set<transform_map>::iterator j = DFA.trans_map.begin(); j != DFA.trans_map.end();j++){ //循环查看当前是否满足对应关系
                    State_Transfer = *j;
                    if((current_state == State_Transfer.now) && (ch_type == State_Transfer.rec)){
                        current_state = State_Transfer.next;
                        strToken.append(1,ch);
                        if(DFA.final.count(current_state)){     //当前是终态时需要进行超前搜索
                            int next_state = -1;
                            transform_map next_State_Transfer;
                            for(set<transform_map>::iterator k = DFA.trans_map.begin(); k != DFA.trans_map.end();k++){  //对于超前搜索的，循环查看当前是否满足对应关系
                                next_State_Transfer = *k;
                                if((current_state == next_State_Transfer.now) && (GetCharType(buf[i+1],buf[i+2]) == next_State_Transfer.rec)) {
                                    next_state = next_State_Transfer.next;
                                    break;
                                }
                            }
                            if(!DFA.final.count(next_state)){
                                cout << strToken << " " << Get_Tokens(current_state,strToken,DFA) << endl;
                                record_tokens << strToken << " " << Get_Tokens(current_state,strToken,DFA) << endl;
                                Generate_symbol_table(current_state,strToken,DFA);
                                current_state = *DFA.start.begin();
                                strToken = "";
                            }
                        }
                        break;
                    }
                }
            }  
        }
    }
    else {                     //未能成功打开则输出错误信息
        cout<<"未能成功打开文件"<<endl;
    }

}

void lexical_analysis(){
    FA NFA, DFA, minDFA;
    NFA.input_symbols = lex_input_symbols;   
    NFA.start = lex_start;
    NFA.final = lex_final;
    NFA.trans_map = lex_trans_map;
    NFA.state_labels = lex_state_labels;
    //cout << "NFA" << endl;
    DFA = NFAdeterminization(NFA);
    //cout << endl << "DFA" << endl; 
    minDFA = minimize(DFA);
   // cout << endl << "minDFA" << endl;
    //cout << endl;
    lexcial("01_var_defn.sy", minDFA,"1");
    lexcial("02_var_defn.sy", minDFA,"2");
    lexcial("03_var_defn.sy", minDFA,"3");
    lexcial("04_var_defn.sy", minDFA,"4");
    lexcial("05_var_defn.sy", minDFA,"5");
    
}

int main(){
    lexical_analysis();
}