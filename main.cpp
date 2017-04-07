#include <iostream>
#include <cstdio>
#include <cstring>
#include <cstdlib>
#include <algorithm>
#include <time.h>
#include <vector>
#include <bitset>
#include <queue>
#include <cmath>
#include <functional>
#include <deque>

using namespace std;

#define MAX_ANS_LENGTH 50010
#define MAX_NODE 1000
#define MAX_EDGE 10000
#define MAX_CONSUME_NODE 500
#define MAX_ANS_LENTH 50010
#define INF 0x3f3f3f3f
#define LOOP_TIME 2e5
#define extraNode1 (numNode)
#define extraNode2 (numNode + 1)
#define Te 100
#define delta 0.995
#define delta2 1.012
#define eps 1e-100
#define BUG(x)  cout << x << endl;

//


#define BACKSTATE
#define NOWCOST
#define TEMPER


//

//
char topo_file[1000][1000];
int dis[MAX_NODE + 10];
bool vis[MAX_NODE + 10];
int consume[MAX_NODE + 10];
int nowLine;
//

typedef struct {
    int nodeId;
    int flowDesired;
}consumeNode;

consumeNode consumeNodes[MAX_NODE + 10];

typedef struct {
    int nodeFirId;
    int nodeSecId;
    int upperFlow;
    int perFlowCost;
}Edge;

struct edgeType {
    int t, cost, flow;
    int rcost, rflow;
    edgeType *next, *pair, *prev;
    edgeType() {}
    edgeType(int T, int C, int F, edgeType* N):t(T), cost(C), flow(F), next(N) {prev = NULL;}
    //edgeType(int T, int C, int F, edgeType* N): t(T), cost(C), flow(F), next(N) {}
} *nodeEdge[MAX_NODE + 10], *pe;

void addEdge(int source, int target, int cost, int flow) {
    struct edgeType *t1 = new struct edgeType(target, cost, flow, nodeEdge[source]);
    if (nodeEdge[source] != NULL) {
        nodeEdge[source]->prev = t1;
    }
    t1->rcost = t1->cost;
    nodeEdge[source] = t1;
    
    struct edgeType *t2 = new struct edgeType(source, -cost, 0, nodeEdge[target]);
    if (nodeEdge[target] != NULL) {
        nodeEdge[target]->prev = t2;
    }
    t2->rcost = t2->cost;
    nodeEdge[target] = t2;
    
    nodeEdge[source] -> pair = nodeEdge[target];
    nodeEdge[target] -> pair = nodeEdge[source];
}

void addEdge2(int source, int target, int cost, int flow1, int flow2) {
    struct edgeType *t1 = new struct edgeType(target, cost, flow1, nodeEdge[source]);
    if (nodeEdge[source] != NULL) {
        nodeEdge[source]->prev = t1;
    }
    nodeEdge[source] = t1;
    struct edgeType *t2 = new struct edgeType(source, -cost, flow2, nodeEdge[target]);
    if (nodeEdge[target] != NULL) {
        nodeEdge[target]->prev = t2;
    }
    nodeEdge[target] = t2;
    nodeEdge[source] -> pair = nodeEdge[target];
    nodeEdge[target] -> pair = nodeEdge[source];
}

int getRandomNum (int upperBound) {
    return rand() % upperBound;
}

double Random () {
    return rand() / (double)RAND_MAX;
}


int aug (int source, int target, int tempNode, int minFlow, int &nowCost, int piS) {
    if (tempNode == target) {
        nowCost += piS * minFlow;
        return minFlow;
    }
    
    vis[tempNode] = true;
    int l = minFlow;
    for (edgeType *i = nodeEdge[tempNode]; i; i = i->next) {
        if (i->flow && !i->cost && !vis[i->t]) {
            int d = aug(source, target, i->t, min(l, i->flow), nowCost, piS);
            i->flow -= d;
            i->pair->flow += d;
            l -= d;
            if (!l) {
                return minFlow;
            }
        }
    }
    return minFlow - l;
    
}

bool changeLabel (int source, int target, int numNode, int &piS) {
    memset(dis, 0x3f, sizeof(dis));
    dis[target] = 0;
    deque<int>Dque;
    Dque.push_back(target);
    while (!Dque.empty()) {
        int tempNode = Dque.front(); Dque.pop_front();
        
        for (edgeType *i = nodeEdge[tempNode]; i; i = i->next) {
            if (i->pair->flow && (dis[tempNode] - i->cost) < dis[i->t]) {
                dis[i->t] = dis[tempNode] - i->cost;
                //spfa better place
                if (dis[i->t] <= dis[Dque.size() ? Dque.front() : 0]) {
                    Dque.push_front(i->t);
                } else {
                    Dque.push_back(i->t);
                }
            }
        }
    }
    
    for (int i = 0; i < numNode + 2; i++) {
        for (edgeType *j = nodeEdge[i]; j; j = j->next) {
            j->cost += dis[j->t] - dis[i];
        }
    }
    piS += dis[source];
    return dis[source] < INF;
}


bool checkNode (int nodeId) {
    // check all the flows out
    
    for (edgeType *i = nodeEdge[nodeId]; i; i = i->next) {
        if (i->flow != 0) {
            return false;
        }
    }
    return true;
}

void freeNode (struct edgeType *temp) {
    //
    if (temp != NULL) {
        freeNode(temp->next);
        if (temp->pair->prev != NULL) {
            temp->pair->prev->next = temp->pair->next;
        } else {
            nodeEdge[temp->t] = temp->pair->next;
        }
        
        if (temp->pair->next != NULL) {
            temp->pair->next->prev = temp->pair->prev;
        }
        
        delete temp->pair;
        delete temp;
    }
}

void backcost(int numNode) {
    for (int i = 0; i < numNode + 2; i++) {
        for (edgeType *j = nodeEdge[i]; j; j = j->next) {
            j->cost = j->rcost;
        }
    }
}

void remFlow(int numNode) {
    for (int i = 0; i < numNode + 2; i++) {
        for (edgeType *j = nodeEdge[i]; j; j = j->next) {
            j->rflow = j->flow;
        }
    }
}

void backFlow(int numNode) {
    for (int i = 0; i < numNode + 2; i++) {
        for (edgeType *j = nodeEdge[i]; j; j = j->next) {
            j->flow = j->rflow;
        }
    }
}

int dfs(int nodeId, int numNode, int minFlow) {
    
    
    if (nodeId >= numNode) {
        for (edgeType *i = nodeEdge[nodeId]; i; i = i->next) {
            if (i->flow > 0) {
                //cout << nodeId << " ";
                int d = min(i->flow, dfs(i->t, numNode, min(minFlow, i->flow)));
                i->flow -= d;
                return d;
            }
        }
    }
    
    for (edgeType *i = nodeEdge[nodeId]; i; i = i->next) {
        if (i->flow > 0 && i->cost < 0) {
            //cout << nodeId << " ";
            sprintf(topo_file[nowLine]+strlen(topo_file[nowLine]),"%d ", nodeId);
            int d = min(i->flow, dfs(i->t, numNode, min(minFlow, i->flow)));
            i->flow -= d;
            return d;
        }
    }
    if (consume[nodeId] != -1) {
        //cout << nodeId << " " << consume[nodeId] << " ";
        sprintf(topo_file[nowLine]+strlen(topo_file[nowLine]),"%d %d ", nodeId, consume[nodeId]);
        return min(minFlow, consumeNodes[consume[nodeId]].flowDesired);
    }
    //consume node
    return INF;
}


int main(int argc, const char * argv[]) {
    
    
    int numNode, numEdge, numConsumeNode;
    int costPerServer;
    int piS;
    int randomNum, randomNum2;
    double startTime = (double)clock() / CLOCKS_PER_SEC;
    double endTime = 108;
    memset(consume, -1, sizeof(consume));
    Edge Edges[MAX_EDGE];
    
    //input begin
    FILE *fin = fopen("/Users/zhaochen/Desktop/huawei/input/case6.txt","rb");
    fscanf(fin,"%d%d%d",&numNode,&numEdge,&numConsumeNode);
    fscanf(fin,"%d",&costPerServer);
    
    for (int i = 0; i < numEdge; i++) {
        int a, b, c, d;
        fscanf(fin,"%d%d%d%d", &a, &b, &c, &d);
        Edges[i].nodeFirId = a;
        Edges[i].nodeSecId = b;
        Edges[i].upperFlow = c;
        Edges[i].perFlowCost = d;
        //Add edges
        addEdge(a, b, d, c);
        addEdge(b, a, d, c);
    }
    
    
    for (int i=0;i<numConsumeNode;i++){
        int x,y,z;
        fscanf(fin,"%d%d%d",&x,&y,&z);
        consumeNodes[x].nodeId=y;
        consumeNodes[x].flowDesired=z;
        consume[y] = x;
    }
    //input end
    int loopTimes = 0;
    int bestCost = 0;
    bool bestAns[MAX_NODE + 10];
    
    int lastCost;
    bool lastAns[MAX_NODE];
    int nowCost;
    bool nowAns[MAX_NODE];
    
    int lastNode = extraNode1;
    int nowNode = extraNode2;
    
    int currentCost = INF;
    
    memset(bestAns, 0, sizeof(bestAns));
    memset(lastAns, 0, sizeof(lastAns));
    memset(nowAns, 0, sizeof(nowAns));
    
    //initial
    lastCost = costPerServer * numConsumeNode;
    bestCost = lastCost;
    nowCost = lastCost;
    for (int i = 0; i < numConsumeNode; i++) {
        lastAns[consumeNodes[i].nodeId] = true;
        
        addEdge2(consumeNodes[i].nodeId, lastNode, 0, INF - consumeNodes[i].flowDesired, consumeNodes[i].flowDesired);
        
    }
    double temper = Te;
    int backTime = 0;
    
    while (1) {
        //count times
        if (loopTimes > LOOP_TIME) {
            break;
        }
        if (temper < eps) {
            break;
        }
        
        bool isBack = false;
        
#ifdef TEMPER
        cout << "temper is :" << temper << endl;
#endif
        
        randomNum = getRandomNum(numNode);
        int numTrue = 0;
        for (int i = 0; i < numNode; i++) {
            if (lastAns[i]) {
                numTrue++;
            }
        }
        
        if (getRandomNum(2) == 0) {
            int tempRandomNum = getRandomNum(numTrue);
            int tempCountNum = 0;
            for (int i = 0; i < numNode; i++) {
                if (lastAns[i]) {
                    if (tempRandomNum == tempCountNum) {
                        randomNum = i;
                        break;
                    }
                    tempCountNum++;
                }
            }
        } else {
            int tempRandomNum = getRandomNum(numNode - numTrue);
            int tempCountNum = 0;
            for (int i = 0; i < numNode; i++) {
                if (!lastAns[i]) {
                    if (tempRandomNum == tempCountNum) {
                        randomNum = i;
                        break;
                    }
                    tempCountNum++;
                }
            }
        }
        
        
        //
        if (lastAns[randomNum]) {
            //Delete point
            cout << "Delete point ";
            for (int i = 0; i < numNode; i++) {
                nowAns[i] = lastAns[i];
            }
            nowAns[randomNum] = false;
            nowCost = lastCost - costPerServer;
            //Add edges
            for (int i = 0; i < numNode; i++) {
                if (nowAns[i]) {
                    addEdge(i, nowNode, 0, INF);
                }
            }
            
            //cout << lastCost << " " << nowCost << endl;
            //mincostflow
            piS = 0;
            remFlow(numNode);
            while (changeLabel(lastNode, nowNode, numNode, piS)) {
                do {
                    memset(vis, 0, sizeof(vis));
                } while (aug(lastNode, nowNode, lastNode, INF, nowCost, piS));
            }
            backcost(numNode);
            
            
            //check all flow out
            if (!checkNode(lastNode)) {
                //back the flow
                backFlow(numNode);
                
                freeNode(nodeEdge[nowNode]);
                nodeEdge[nowNode] = NULL;
                
                isBack = true;
                
            } else if (nowCost > lastCost) {
                //
                if (exp((double)(lastCost - nowCost) * numNode * 5 / bestCost /temper) < Random() ) {
                    
                    //backFlow(roadId, flowMap, costMap);
                    backFlow(numNode);
                    
                    freeNode(nodeEdge[nowNode]);
                    nodeEdge[nowNode] = NULL;
                    
                    isBack = true;
                    
                }
                
            }
            
            //
            
            
        } else {
            //Add point
            cout << "Add point " ;
            for (int i = 0; i < numNode; i++) {
                nowAns[i] = lastAns[i];
            }
            nowAns[randomNum] = true;
            nowCost = lastCost + costPerServer;
            //Add edges
            for (int i = 0; i < numNode; i++) {
                if (nowAns[i]) {
                    addEdge(i, nowNode, 0, INF);
                }
            }
            
            //mincostflow
            piS = 0;
            remFlow(numNode);
            while (changeLabel(lastNode, nowNode, numNode, piS)) {
                do {
                    memset(vis, 0, sizeof(vis));
                } while (aug(lastNode, nowNode, lastNode, INF, nowCost, piS));
            }
            backcost(numNode);
            
            if (nowCost > lastCost) {
                //
                if (exp((double)(lastCost - nowCost) * numNode * 5 / bestCost /temper) < Random()) {
                    
                    //backFlow(roadId, flowMap, costMap);
                    backFlow(numNode);
                    
                    freeNode(nodeEdge[nowNode]);
                    nodeEdge[nowNode] = NULL;
                    
                    isBack = true;
                    
                }
                
            }
            
        }
        
        
        
#ifdef BACKSTATE
        if (isBack) {
            cout << "isBack" << endl;
        } else {
            cout << "notBack" << endl;
        }
#endif
        
        //
        if (nowCost < bestCost && !isBack) {
            bestCost = nowCost;
            for (int i = 0; i < numNode; i++) {
                bestAns[i] = nowAns[i];
            }
        }
        
        if (!isBack) {
            backTime = 0;
        } else {
            backTime++;
        }
        
        
        
        if (backTime > 30 && (double)clock() / CLOCKS_PER_SEC - startTime <= endTime - 20) {
            temper *= delta2;
            //temper = 100;
            cout << "add temper : " << loopTimes << endl;
        }
        
        if (!isBack) {
            freeNode(nodeEdge[lastNode]);
            nodeEdge[lastNode] = NULL;
            swap(lastNode, nowNode);
            swap(lastCost, nowCost);
            for (int i = 0; i < numNode; i++) {
                lastAns[i] = nowAns[i];
            }
        }
        
        //
        loopTimes++;
        temper *= delta;
        
        if ((double)clock() / CLOCKS_PER_SEC - startTime >= endTime) {
            break;
        }
        
#ifdef NOWCOST
        cout << nowCost << " " << bestCost << endl;
#endif
        
    }
    
    int tempCount = 0;
    for (int i = 0; i < numNode; i++) {
        if (bestAns[i]) {
            tempCount++;
        }
    }
    
    cout << "loopTimes : " << loopTimes << " servernum: " << tempCount << "  bestCost : " << bestCost << " time : " << (double)clock() / CLOCKS_PER_SEC - startTime << endl;
    
    for (int i = 0; i < numNode; i++) {
        if (bestAns[i]) {
            addEdge(i, nowNode, 0, INF);
        }
    }
    piS = 0;
    while (changeLabel(lastNode, nowNode, numNode, piS)) {
        do {
            memset(vis, 0, sizeof(vis));
        } while (aug(lastNode, nowNode, lastNode, INF, nowCost, piS));
    }
    backcost(numNode);
    
    //out file
    
    /*
     while (!checkNode(nowNode)) {
     //there exit some flow
     int d = dfs(nowNode, numNode, INF);
     cout << d << endl;
     }
     */
    
    return 0;
}












