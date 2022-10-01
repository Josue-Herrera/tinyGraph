
#include <unordered_map>
#include <vector>
#include <iostream>
#include <limits>
#include <tuple>
#include <algorithm>
#include <set>

template<class Graph_Types, class K, class V>
struct graph_typed : std::unordered_map<K, V> {
    using graph_types = Graph_Types;
};

template<class V_t, class W_t>
struct graph_types_t {
    using key_type    = V_t;
    using mapped_type = std::vector<std::tuple<V_t,W_t>>;
    using vertex_type = V_t;
    using weight_type = W_t;
    using graph_type  = graph_typed<graph_types_t<V_t, W_t>, key_type, mapped_type>;
    using weight_and_vertex_type = std::tuple<W_t,V_t>;

    template<class Comp>
    class priority_queue {
        using container_t = std::vector<weight_and_vertex_type>;
        container_t c;    
        Comp comp;   
    public:
        void reserve(std::size_t size) noexcept {  c.reserve(size);  }
        bool empty() const noexcept(noexcept(c.empty())) { return c.empty(); }
        auto size() const noexcept(noexcept(c.size())) { return c.size(); }
        auto const& top() const noexcept(noexcept(c.front())) { return c.front(); }

        void push(const weight_and_vertex_type& _Val) noexcept {
            c.push_back(_Val);
            std::push_heap(c.begin(), c.end(), comp);
        }

        void push(weight_and_vertex_type&& _Val) noexcept {
            c.push_back(std::move(_Val));
            std::push_heap(c.begin(), c.end(), comp);
        }

        template <class... _Valty>
        void emplace(_Valty&&... _Val) noexcept {
            c.emplace_back(std::forward<_Valty>(_Val)...);
            std::push_heap(c.begin(), c.end(), comp);
        }

        void pop() noexcept {
            std::pop_heap(c.begin(), c.end(), comp);
            c.pop_back();
        }
    };
};

template<class T>
using vertex_t = typename T::vertex_type; 

template<class T>
using weight_t = typename T::weight_type;

template<class T>
using weight_limit_t  = std::numeric_limits<weight_t<T>>;

template<class T>
using value_t  = typename T::mapped_type; 

template<class T>
using graph_t  = typename T::graph_type; 

template<class T>
using inner_graph_types_t  = typename T::graph_types; 

template<class T>
using wv_t     = typename T::weight_and_vertex_type; 

template<class T>
using wv_t     = typename T::weight_and_vertex_type; 

template<class T, class Comp>
using priority_queue  = typename T::template priority_queue<Comp>; 

// end of header

//C++17 Fold Expressions and C++11 Variadic Template and Universal References (&&)
template<class Graph, class... Ts>
void add_links(Graph& G, Ts&&... ts){
    ((G[ts.first] = ts.second), ...);
}

/// @brief  Disjkstras Shortest Path Algorithm is a
//          Greedy Algorithm using the minimum distance from each vertex as heuristic. 
/// @param G graph data structure
/// @param start starting vertex of graph to start search.
/// @param finish vertex being looked for from start vertex.
/// @return std::tuple { weight_t { shortest distance }, std::vector<vertex_id_t> { shortest path from start to finish } };
template<class Graph_t, class Vertex>
auto dijkstra_shortest_path_old (Graph_t const& G, Vertex const& start, Vertex const& finish) {
    using Graph            = inner_graph_types_t<Graph_t>;
    using dijkstra_table_t = std::unordered_map<vertex_t<Graph>, wv_t<Graph>>;
    using visited_t        = std::vector<vertex_t<Graph>>;
    using result_t         = std::vector<vertex_t<Graph>>;

    dijkstra_table_t  table{};
    visited_t         visited{};
    visited_t         unvisited{};
    result_t          result{};

    // Helper Functions to extract values out of table
    auto get_distance = [&](auto& vertex){ return std::get<0>(table[vertex]); };
    auto get_previous = [&](auto& vertex){ return std::get<1>(table[vertex]); };

    // allocate the size of all the auxillury data structures based on the graph size.
    auto graph_size = G.size();
    table.reserve(graph_size);
    visited.reserve(graph_size);
    unvisited.reserve(graph_size);
    result.reserve(graph_size);

    // default initialize dijkstra's table and unvisited collection 
    for(auto& [from, edges] : G)  {
          table[from] = { weight_limit_t<Graph>::max(), 0 };
          unvisited.emplace_back(from);
    }

    // set the starting distance to itself to zero
    table[start] = { 0.0, start };
    
    // create a empty current 
    vertex_t<Graph>  current {}; 
    while (visited.size() < graph_size) {
        
        // Finding the next vertex to visit is based on the minimum
        // shortest distance from the start that you havent visited yet
        // Lines 97 - 99 can make this a greedy algorithm using the first minimum
        // distance as a heuristic. 
        // NOTE: this can be passed in as function to change the behavior! 
        // (e.g Shortest Path of the Max Distance) 
        auto min_unvisited_vertex = [&](auto& l, auto& r){ return get_distance(l) < get_distance(r); };
        current = *std::min_element(unvisited.begin(), unvisited.end(), min_unvisited_vertex);

        // if your next node is being searched it means you 
        // have found the minimum path the finish vertex
        if (current == finish) break;

        // Find the Current Vertex's shortest starting distance and Previous vertex.
        auto& [start_dist, prev] = table[current];

        // Find the current Vertex's Neighbors with their distances.
        for (auto& [neighbor, dist] : G.at(current)) {
        
            // Find the neighbor's shorest distance and associated vertex 
            auto& [shortest_dist, prev_vert] = table[neighbor];
            
            // calculate the distance of the of each neigbhor from the start.
            auto distance_from_start = start_dist + dist; // start_dist + heuristic(neighbor);

            // if the distance from the start is less than the shortest distance 
            // to that neighbor then update the table with the new shortest distance
            // and what vertex was the cause of it.
            if (distance_from_start < shortest_dist) 
                table[neighbor] = { distance_from_start, current };
        }

        // Add Current Vertex To visited Set
        visited.emplace_back(current);

        // Remove current vertex from unvisited 
        auto removed_current = std::remove(std::begin(unvisited), std::end(unvisited), current);
        unvisited.erase(removed_current, std::end(unvisited));
    }

    // Back track to fill the Shortest Path 
    current = finish;
    while (current != start) {
        result.emplace_back(current);
        current = get_previous(current);
    }
    result.emplace_back(start);
    std::reverse(result.begin(), result.end());
    return std::tuple { get_distance(finish), result };
}


/// @brief  Disjkstras Shortest Path Algorithm is a
//          Greedy Algorithm using the minimum distance from each vertex as heuristic. 
/// @param G graph data structure
/// @param start starting vertex of graph to start search.
/// @param finish vertex being looked for from start vertex.
/// @return std::tuple { weight_t { shortest distance }, std::vector<vertex_id_t> { shortest path from start to finish } };
template<class Graph_t, class Vertex>
auto dijkstra_shortest_path (Graph_t const& G, Vertex const& start, Vertex const& finish) {
    using Graph            = inner_graph_types_t<Graph_t>;
    using dijkstra_table_t = std::unordered_map<vertex_t<Graph>, wv_t<Graph>>;
    using visited_t        = std::set<vertex_t<Graph>>;
    auto  weighted_greater = [](auto const& wv1, auto const& wv2) { return std::get<0>(wv1) > std::get<0>(wv2); };
    using unvisited_t      = priority_queue<Graph, decltype(weighted_greater)>;
    using result_t         = std::vector<vertex_t<Graph>>;

    dijkstra_table_t  table{};
    visited_t         visited{};
    unvisited_t       unvisited{};
    result_t          result{};

    // Helper Functions to extract values out of table
    auto get_distance = [&](auto& vertex){ return std::get<0>(table[vertex]); };
    auto get_previous = [&](auto& vertex){ return std::get<1>(table[vertex]); };

    // allocate the size of all the auxillury data structures based on the graph size.
    auto graph_size = G.size();
    table.reserve(graph_size);
    result.reserve(graph_size);
    unvisited.reserve(graph_size);

    // default initialize dijkstra's table and unvisited collection 
    for(auto& [from, edges] : G) table[from] = { weight_limit_t<Graph>::max(), 0 };
    
    // set the starting distance to itself to zero
    table[start] = { 0.0, start };
    unvisited.emplace(0, start);
    
    // create a empty current 
    vertex_t<Graph>  current {}; 
    while (visited.size() < graph_size) {
        
        // Finding the next vertex to visit is based on the minimum
        // shortest distance from the start that you havent visited yet
        // Lines 97 - 99 can make this a greedy algorithm using the first minimum
        // distance as a heuristic. 
        // NOTE: this can be passed in as function to change the behavior! 
        // (e.g Shortest Path of the Max Distance) 
        do {
            current = std::get<1>(unvisited.top());
            unvisited.pop();
        } while (visited.find(current) != std::end(visited));

        // if your next node is being searched it means you 
        // have found the minimum path the finish vertex
        if (current == finish) break;

        // Find the Current Vertex's shortest starting distance and Previous vertex.
        auto& [start_dist, prev] = table[current];

        // Find the current Vertex's Neighbors with their distances.
        for (auto& [neighbor, dist] : G.at(current)) {
        
            // Find the neighbor's shorest distance and associated vertex 
            auto& [shortest_dist, prev_vert] = table[neighbor];
            
            // calculate the distance of the of each neigbhor from the start.
            auto distance_from_start = start_dist + dist; // start_dist + heuristic(neighbor);

            // if the distance from the start is less than the shortest distance 
            // to that neighbor then update the table with the new shortest distance
            // and what vertex was the cause of it.
            if (distance_from_start < shortest_dist) {
                table[neighbor] = { distance_from_start, current };
                unvisited.emplace(distance_from_start, neighbor);
            }
        }

        // Add Current Vertex To visited Set
        visited.emplace(current);
    }

    // Back track to fill the Shortest Path 
    current = finish;
    while (current != start) {
        result.emplace_back(current);
        current = get_previous(current);
    }
    result.emplace_back(start);
    std::reverse(result.begin(), result.end());
    return std::tuple { get_distance(finish), result };
}


void d_graph_test() {
    using Graph = graph_types_t<char, double>;
    graph_t<Graph> G{};

    add_links(G,
        std::pair { 'A', value_t<Graph>{ {'B', 6.0}, {'D', 1.0} } },
        std::pair { 'B', value_t<Graph>{ {'A', 6.0}, {'C', 5.0}, {'E', 2.0}, {'D', 2.0}  } },
        std::pair { 'C', value_t<Graph>{ {'B', 5.0}, {'E', 5.0} }},
        std::pair { 'D', value_t<Graph>{ {'A', 1.0}, {'B', 2.0}, {'E', 1.0} } },
        std::pair { 'E', value_t<Graph>{ {'B', 2.0}, {'C', 5.0}, {'D', 1.0} } }
    );

    printf("\n\n");
    for(auto& [from, edges] : G) {
        printf("[from: %c] -> [", from);
        for(auto& [to,  weight]: edges) {
            printf("(to: %c, cost: %f) ", to, weight);
        }
        printf("]\n");
    }

    vertex_t<Graph> start  = 'A';
    vertex_t<Graph> finish = 'C';
    auto [min_distance, shortest_path] = dijkstra_shortest_path(G, start, finish);
    printf("Minimum Distance From %c to %c : %f \n", start, finish, min_distance);
    printf("Shortest Path    From %c to %c : [ ", start, finish);
    for(auto& vertex : shortest_path) printf("%c ", vertex);
    printf("]\n");
}

void graph_test(){
    using Graph = graph_types_t<int, double>;
    graph_t<Graph> G{};

    add_links(G,
        std::pair { 1, value_t<Graph>{ {2, 1.0}, {7, 10.0} } },
        std::pair { 2, value_t<Graph>{ {3, 6.0}, {6, 3.0} } },
        std::pair { 3, value_t<Graph>{ {4, 5.0} } },
        std::pair { 4, value_t<Graph>{ {5, 10.0} } },
        std::pair { 5, value_t<Graph>{ } },
        std::pair { 6, value_t<Graph>{ {4, 9.0}, {8, 9.0} } },
        std::pair { 7, value_t<Graph>{ {9, 3.0}} },
        std::pair { 8, value_t<Graph>{ {5, 9.0} } },
        std::pair { 9, value_t<Graph>{ {8, 6.0} } }
    );

     printf("\n\n");
    // [from: 1] -> [(to: 2, cost: 1.0) (to: 7, cost: 10.0)]
    // c++17 Structured Bindings 
    for(auto& [from, edges] : G) {
        printf("[from: %d] -> [", from);
        for(auto& [to,  weight]: edges) {
            printf("(to: %d, cost: %f) ", to, weight);
        }
        printf("]\n");
    }

    vertex_t<Graph> start  = 1;
    vertex_t<Graph> finish = 5;

    auto [min_distance, shortest_path] = dijkstra_shortest_path(G, start, finish);

    printf("Minimum Distance From %d to %d : %f \n", start, finish, min_distance);

    printf("Shortest Path    From %d to %d : [ ", start, finish);
    for(auto& vertex : shortest_path) printf("%d ", vertex);
    printf("]\n");

};

int main () {

    d_graph_test();
    graph_test();
    return 0;
}