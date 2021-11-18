#include <iostream>
#include <string>
#include <vector>
#include <fstream>
#include <sstream>
#include <set>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <queue>
#include <chrono>
#include <map>
#include <climits>
#include <algorithm>
#include <random>
using namespace std;

typedef pair<int, int> PII;

/**
 * @brief Get the Graph object
 * 
 * @param filename Graph data file
 * @param hyperEdge Point set corresponding to hyperedge
 * @param hyperNode Edge set corresponding to hypernode
 */
void getGraph(const string &filename, vector<vector<int> > &hyperEdge, unordered_map<int, vector<int> > &hyperNode)
{
    ifstream fin(filename, ios::in);
    int count = -1;
    while (true)
    {
        string str;
        getline(fin, str);
        if (str == "")
            break;
        istringstream ss(str);
        int tmp;
        vector<int> e;
        while (ss >> tmp)
        {
            if (find(e.begin(), e.end(), tmp) == e.end())
                e.push_back(tmp);
        }
        if (e.size() == 1)
            continue;
        count++;
        hyperEdge.push_back(e);
        for (auto &node : e)
            hyperNode[node].push_back(count);
    }
}

/**
 * @brief Arrange the pair.second in ascending order
 * 
 */
struct myCmp
{
    bool operator()(const pair<int, int> &a, const pair<int, int> &b) const
    {
        if (a.first == b.first)
            return false;
        else
        {
            if (a.second != b.second)
                return a.second < b.second;
            else
                return a.first < b.first;
        }
    }
};

/**
 * @brief K-core decomposition of hypergraph
 * 
 * @param hyperEdge Point set corresponding to hyperedge
 * @param hyperNode Edge set corresponding to hypernode
 * @param core K-core value of hypernode
 */
void kcoreDecomp(vector<vector<int> > &hyperEdge, unordered_map<int, vector<int> > &hyperNode, unordered_map<int, int> &core)
{
    core.clear();
    set<pair<int, int>, myCmp> node_count;
    unordered_map<int, int> deg;
    vector<bool> visitEdge(hyperEdge.size(), false);
    unordered_map<int, bool> visitNode;
    for (auto &it : hyperNode)
    {
        deg[it.first] = it.second.size();
        node_count.insert(make_pair(it.first, deg[it.first]));
        visitNode[it.first] = false;
    }
    int K = 0;
    while (!node_count.empty())
    {
        pair<int, int> p = *node_count.begin();
        node_count.erase(node_count.begin());
        K = max(K, p.second);
        core[p.first] = K;
        visitNode[p.first] = true;
        for (auto &edge : hyperNode[p.first])
        {
            if (visitEdge[edge])
                continue;
            visitEdge[edge] = true;
            for (auto &node : hyperEdge[edge])
            {
                if (visitNode[node])
                    continue;
                if (node_count.erase(make_pair(node, deg[node])))
                {
                    deg[node]--;
                    node_count.insert(make_pair(node, deg[node]));
                }
            }
        }
    }
}

/**
 * @brief H-core decomposition of hypergraph
 * 
 * @param hyperEdge Point set corresponding to hyperedge
 * @param hyperNode Edge set corresponding to hypernode
 * @param core H-core value of hypernode
 */
void hCoreDecomp(vector<vector<int> > &hyperEdge, unordered_map<int, vector<int> > &hyperNode, unordered_map<int, int> &core)
{
    core.clear();
    unordered_map<int, unordered_map<int, int> > nbr;
    set<pair<int, int>, myCmp> s;
    for (auto &it : hyperNode)
    {
        for (auto &edge : it.second)
        {
            for (auto &node : hyperEdge[edge])
            {
                nbr[it.first][node]++;
            }
        }
        nbr[it.first].erase(it.first);
        s.insert(make_pair(it.first, nbr[it.first].size()));
    }
    int k = 0;
    vector<bool> visitEdge(hyperEdge.size(), false);
    unordered_map<int, bool> visitNode;
    while (!s.empty())
    {
        pair<int, int> p = *s.begin();
        s.erase(s.begin());
        k = max(k, p.second);
        core[p.first] = k;
        visitNode[p.first] = true;
        for (auto &edge : hyperNode[p.first])
        {
            if (visitEdge[edge])
                continue;
            visitEdge[edge] = true;

            for (int i = 0; i < hyperEdge[edge].size(); i++)
            {
                int v = hyperEdge[edge][i];
                if (v == p.first)
                    continue;
                if (!visitNode[v])
                    s.erase(make_pair(v, nbr[v].size()));
                for (int j = 0; j < hyperEdge[edge].size(); j++)
                {
                    int u = hyperEdge[edge][j];
                    if (v == u)
                        continue;
                    nbr[v][u]--;
                    if (nbr[v][u] == 0)
                        nbr[v].erase(u);
                }
                if (!visitNode[v])
                    s.insert(make_pair(v, nbr[v].size()));
            }
        }
        nbr[p.first].clear();
    }
}

/**
 * @brief Degree of hypernode in the hypergraph
 * 
 * @param hyperEdge Point set corresponding to hyperedge
 * @param hyperNode Edge set corresponding to hypernode
 * @param core Degree value of hypernode
 */
void deg(vector<vector<int> > &hyperEdge, unordered_map<int, vector<int> > &hyperNode, unordered_map<int, int> &core)
{
    core.clear();
    for (auto &it : hyperNode)
    {
        core[it.first] = it.second.size();
    }
}

/**
 * @brief Number of neighbors of hypernode in the hypergraph
 * 
 * @param hyperEdge Point set corresponding to hyperedge
 * @param hyperNode Edge set corresponding to hypernode
 * @param core The number of neighbors of hypernode
 */
void nbr(vector<vector<int> > &hyperEdge, unordered_map<int, vector<int> > &hyperNode, unordered_map<int, int> &core)
{
    core.clear();
    unordered_map<int, unordered_set<int> > nbr;
    for (auto &it : hyperNode)
    {
        for (auto &edge : it.second)
        {
            for (auto &node : hyperEdge[edge])
                nbr[it.first].insert(node);
        }
    }
    for (auto &it : nbr)
    {
        core[it.first] = it.second.size() - 1;
    }
}

/**
 * @brief The number of hypernode corresponding to the value
 * 
 * @param core Value of hypernode
 * @param num The number of hypernode corresponding to the value
 */
void computeCore(const unordered_map<int, int> &core, map<int, int> &num)
{
    num.clear();
    for (auto &it : core)
    {
        num[it.second]++;
    }
}

/**
 * @brief The number of hypernode corresponding to the k-core, h-core, degree and num of neighbors value of a hypergraph
 * 
 * @return int 
 */
int main()
{
    string file = "S_DrAb  S_MaAn  S_MiAc S_TrCl  S_WaTr  T_CoMH  T_ThAU  T_ThMS T_DBLP T_congress-bills";
    string filepath = "C++Projects/graphData/";
    istringstream ss(file);
    string str;
    while (ss >> str)
    {
        string filename = filepath + str;
        vector<vector<int> > hyperEdge;
        unordered_map<int, vector<int> > hyperNode;
        unordered_map<int, int> core;
        map<int, int> num;
        getGraph(filename, hyperEdge, hyperNode);
        cout << str << " has read!" << endl;
        cout << "edge is " << hyperEdge.size() << "  node is " << hyperNode.size() << endl;
        deg(hyperEdge, hyperNode, core);
        computeCore(core, num);
        vector<int> x;
        vector<int> y;
        ofstream fout("result/" + str + "/" + str + "-deg.txt");
        x.clear();
        y.clear();
        for (auto &it : num)
        {
            x.push_back(it.first);
            y.push_back(it.second);
        }
        for (auto &it : x)
            fout << it << ' ';
        fout << endl;
        for (auto &it : y)
            fout << it << ' ';
        fout << endl;
        fout.close();
        cout << "deg is finished!" << endl;

        nbr(hyperEdge, hyperNode, core);
        computeCore(core, num);
        fout.open("result/" + str + "/" + str + "-nbr.txt");
        x.clear();
        y.clear();
        for (auto &it : num)
        {
            x.push_back(it.first);
            y.push_back(it.second);
        }
        for (auto &it : x)
            fout << it << ' ';
        fout << endl;
        for (auto &it : y)
            fout << it << ' ';
        fout << endl;
        fout.close();
        cout << "nbr is finished!" << endl;

        kcoreDecomp(hyperEdge, hyperNode, core);
        computeCore(core, num);
        fout.open("result/" + str + "/" + str + "-kcore.txt");
        x.clear();
        y.clear();
        for (auto &it : num)
        {
            x.push_back(it.first);
            y.push_back(it.second);
        }
        for (auto &it : x)
            fout << it << ' ';
        fout << endl;
        for (auto &it : y)
            fout << it << ' ';
        fout << endl;
        fout.close();
        cout << "kcore is finished!" << endl;

        hCoreDecomp(hyperEdge, hyperNode, core);
        computeCore(core, num);
        fout.open("result/" + str + "/" + str + "-hcore.txt");
        x.clear();
        y.clear();
        for (auto &it : num)
        {
            x.push_back(it.first);
            y.push_back(it.second);
        }
        for (auto &it : x)
            fout << it << ' ';
        fout << endl;
        for (auto &it : y)
            fout << it << ' ';
        fout << endl;
        fout.close();
        cout << "hcore is finished!" << endl;
        cout << str << " has finished!" << endl;
    }
}