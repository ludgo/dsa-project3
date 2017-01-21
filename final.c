#define _CRT_SECURE_NO_WARNINGS


#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>

#define DIMENSIONS 2
#define PATH_UNIT 96 // memory unit
#define TELEPORT_UNIT 32 // memory unit
#define PRINCESS_MAX 10
#define SPECIALS 3
#define TOTAL PRINCESS_MAX+SPECIALS
#define START_X 0
#define START_Y 0


// graph adjacency list node representation
typedef struct adjacencyListNode {
	int destination;
	int distance;
	struct adjacencyListNode* next;
} NODE;

// graph adjacency list representation
typedef struct adjacencyList {
	NODE *head;
} LIST;

// graph representation
typedef struct graph {
	int vertices;
	LIST *list;
} GRAPH;

// minimal heap node representation
typedef struct minHeapNode {
	int vertex;
	int distance;
} HEAPNODE;

// minimal heap representation
typedef struct minHeap {
	int size;
	int capacity;
	int *position;
	HEAPNODE **nodes;
} HEAP;

// a single digit teleports representation
typedef struct teleport {
	int index;
	int capacity;
	int *items;
} TELEPORT;


GRAPH *mapGraph;
int *paths[2 * (TOTAL - 1)], *graphPath; // dijkstra result paths
int distBasic[TOTAL][TOTAL], distGenerated[TOTAL][TOTAL]; // matrices of distances between special nodes
char **vars;
int varsCount;

int dragon[DIMENSIONS], generator[DIMENSIONS], princesses[DIMENSIONS * PRINCESS_MAX], princessCount; // specials coordinates
TELEPORT **teleports;

int fields;
int cols;
int *path, pathLength, pathIndex;


// calculate n!
int factorial(n) {
	int i, result;

	result = 1;
	for (i = 1; i <= n; i++) {
		result *= i;
	}
	return result;
}

// swap characters in memory
void swapChars(char *a, char *b) {
	char temp;

	temp = *a;
	*a = *b;
	*b = temp;
}

// calculate sum of integer array
int sumArray(int *array, int length) {
	int i, sum;

	sum = 0;
	for (i = 0; i < length; i++) {
		sum += array[i];
	}
	return sum;
}


// convert coordinates to single index
int graphIndex(int mapIndexX, int mapIndexY) {
	return mapIndexX * cols + mapIndexY;
}

// convert single index to coordinate X
int mapIndexX(int graphIndex) {
	return graphIndex / cols;
}

// convert single index to coordinate Y
int mapIndexY(int graphIndex) {
	return graphIndex % cols;
}


// represent starting character of special field with index
int matrixIndex(char c) {
	switch (c) {
	case 'D': {
		return 0;
	}
	case 'G': {
		return 1;
	}
	case 'S': {
		return 2;
	}
	default: {
		return SPECIALS + c - '1';
	}
	}
}

// get starting character of special field from index
char matrixChar(int index) {
	switch (index) {
	case 0: {
		return 'D';
	}
	case 1: {
		return 'G';
	}
	case 2: {
		return 'S';
	}
	default: {
		return index - SPECIALS + '1';
	}
	}
}


// adjacency list node constructor
NODE *createNode(int destination, int distance) {
	NODE *node;

	node = (NODE *)malloc(sizeof(NODE));
	node->destination = destination;
	node->distance = distance;
	node->next = NULL;
	return node;
}

// graph constructor
GRAPH *createGraph(int vertices) {
	int i;
	GRAPH *graph;
	
	graph = (GRAPH *)malloc(sizeof(GRAPH));
	graph->vertices = vertices;
	graph->list = (LIST *) malloc(vertices * sizeof(LIST));
	for (i = 0; i < vertices; i++) {
		graph->list[i].head = NULL;
	}
	return graph;
}

// minimal heap node constructor
HEAPNODE *createHeapNode(int vertex, int distance) {
	HEAPNODE *minHeapNode;

	minHeapNode = (HEAPNODE *)malloc(sizeof(HEAPNODE));
	minHeapNode->vertex = vertex;
	minHeapNode->distance = distance;
	return minHeapNode;
}

// minimal heap constructor
HEAP *createHeap(int capacity) {
	HEAP *minHeap;

	minHeap = (HEAP *)malloc(sizeof(HEAP));
	minHeap->position = (int *)malloc(capacity * sizeof(int));
	minHeap->size = 0;
	minHeap->capacity = capacity;
	minHeap->nodes = (HEAPNODE **)malloc(capacity * sizeof(HEAPNODE *));
	return minHeap;
}


// add edge to undirected graph
void addEdge(GRAPH *graph, int source, int destination, int distance) {
	NODE *node;

	// add edge from source to destination
	node = createNode(destination, distance);
	node->next = graph->list[source].head;
	graph->list[source].head = node;

	// add edge from destination to source
	node = createNode(source, distance);
	node->next = graph->list[destination].head;
	graph->list[destination].head = node;
}

// swap minimal heap nodes in memory
void swapHeapNodes(HEAPNODE **a, HEAPNODE **b) {
	HEAPNODE *temp = *a;
	*a = *b;
	*b = temp;
}

// modify minimal heap to be able to extract minimum
void minHeapify(HEAP *heap, int index) {
	HEAPNODE *minNode, *indexNode;
	int minimum, left, right;
	
	minimum = index;
	left = 2 * index + 1;
	right = 2 * index + 2;

	// compare with left child
	if (left < heap->size && heap->nodes[left]->distance < heap->nodes[minimum]->distance) {
		minimum = left;
	}

	// compare with right child
	if (right < heap->size && heap->nodes[right]->distance < heap->nodes[minimum]->distance) {
		minimum = right;
	}

	if (minimum != index) {
		// move minimum to root
		minNode = heap->nodes[minimum];
		indexNode = heap->nodes[index];

		heap->position[minNode->vertex] = index;
		heap->position[indexNode->vertex] = minimum;

		swapHeapNodes(&heap->nodes[minimum], &heap->nodes[index]);

		minHeapify(heap, minimum);
	}
}

// return 1 if minimal heap is empty
int isHeapEmpty(HEAP *heap) {
	if (heap->size == 0) {
		return 1;
	}
	return 0;
}

// obtain minimum from minimal heap
HEAPNODE *extractMinimum(HEAP *heap) {
	HEAPNODE *root, *lastNode;

	if (isHeapEmpty(heap) == 1) {
		return NULL;
	}

	// root is minimum
	root = heap->nodes[0];

	// last node is new root
	lastNode = heap->nodes[heap->size - 1];
	heap->nodes[0] = lastNode;

	heap->position[root->vertex] = heap->size - 1;
	heap->position[lastNode->vertex] = 0;

	// heapify
	heap->size--;
	minHeapify(heap, 0);

	return root;
}

// update distances in minimal heap
void decreaseKey(HEAP *heap, int vertex, int distance) {
	int i;

	// update distance for given node
	i = heap->position[vertex];
	heap->nodes[i]->distance = distance;

	// heapify
	while (i && heap->nodes[i]->distance < heap->nodes[(i - 1) / 2]->distance) {
		heap->position[heap->nodes[i]->vertex] = (i - 1) / 2;
		heap->position[heap->nodes[(i - 1) / 2]->vertex] = i;
		swapHeapNodes(&heap->nodes[i], &heap->nodes[(i - 1) / 2]);

		i = (i - 1) / 2;
	}
}

// return 1 if vrtex in minimal heap
int isInHeap(HEAP *heap, int vertex) {
	if (heap->position[vertex] < heap->size) {
		return 1;
	}
	return 0;
}


// inilialize memory for information about teleports
void initTeleports() {

	int i, total;

	total = '9' - '0' + 1;
	teleports = (TELEPORT **)malloc(total * sizeof(TELEPORT *));

	// a single struct instance for each digit
	for (i = 0; i < total; i++) {
		teleports[i] = (TELEPORT *)malloc(sizeof(TELEPORT));
		teleports[i]->index = 0;
		teleports[i]->capacity = TELEPORT_UNIT;
		teleports[i]->items = (int *)malloc(teleports[i]->capacity * sizeof(int));
	}
}

// save information about teleport
void addTeleport(char digit, int x, int y) {

	TELEPORT *teleport;

	teleport = teleports[digit - '0'];

	if (teleport->capacity >= teleport->index) {
		teleport->capacity += TELEPORT_UNIT;
		teleport->items = (int *)realloc(teleport->items, teleport->capacity * sizeof(int));
	}

	teleport->items[teleport->index] = x;
	teleport->items[teleport->index + 1] = y;
	teleport->index += 2;
}

// add teleport edges to graph
void lauchTeleports() {

	TELEPORT *teleport;
	int i, j, k, total;

	total = '9' - '0' + 1;

	for (i = 0; i < total; i++) {
		teleport = teleports[i];
		for (j = 0; j < teleport->index; j += 2) {
			for (k = j; k < teleport->index; k += 2) {
				if (j != k) {
					// weight 0
					addEdge(mapGraph, graphIndex(teleport->items[j], teleport->items[j + 1]), graphIndex(teleport->items[k], teleport->items[k + 1]), 0);
				}
			}
		}
	}
}


// initialize memory for information about path
void initPath() {
	pathLength = PATH_UNIT;
	path = (int *)malloc(pathLength * sizeof(int));
	pathIndex = 0;
}

// add step to path
void addToPath(int x, int y) {
	if (pathIndex >= pathLength) {
		pathLength += PATH_UNIT;
		path = (int *)realloc(path, pathLength * sizeof(int));
	}

	path[pathIndex] = y;
	path[pathIndex + 1] = x;
	pathIndex += 2;
}

// add subpath between 2 points to path
void addSubPath(int graphIndex) {

	if (graphPath[graphIndex] == -1) {
		addToPath(mapIndexX(graphIndex), mapIndexY(graphIndex));
		return;
	}

	addSubPath(graphPath[graphIndex]);

	addToPath(mapIndexX(graphIndex), mapIndexY(graphIndex));
}

// add subpath between 2 points to path in reversed order
void addSubPathRev(int graphIndex) {

	if (graphPath[graphIndex] == -1) {
		addToPath(mapIndexX(graphIndex), mapIndexY(graphIndex));
		return;
	}

	addToPath(mapIndexX(graphIndex), mapIndexY(graphIndex));

	addSubPathRev(graphPath[graphIndex]);
}


// determine field type
void check(char c, int x, int y) {

	if (c >= '0' && c <= '9') {
		addTeleport(c, x, y);
		return;
	}

	switch (c) {
	case 'P': {
		princesses[2 * princessCount] = x;
		princesses[2 * princessCount + 1] = y;
		princessCount++;
		break;
	}
	case 'D': {
		dragon[0] = x;
		dragon[1] = y;
		break;
	}
	case 'G': {
		generator[0] = x;
		generator[1] = y;
		break;
	}
	default: {
		break;
	}
	}
}

// determine graph edge weight from map
int measure(char a, char b) {
	if (a == 'N' || b == 'N') {
		return -1;
	}
	else if (a == 'H' && b == 'H') {
		return 4;
	}
	else if (a == 'H' || b == 'H') {
		return 3;
	}
	else {
		return 2;
	}
}

// convert map to graph
void loadMap(char **map, int n, int m) {

	int i, j, distance;

	cols = m;
	fields = n * m;
	mapGraph = createGraph(fields);
	princessCount = 0;

	for (i = 0; i < n; i++) {
		for (j = 0; j < m; j++) {
			check(map[i][j], i, j);
			if (j != m - 1) {
				// edge between field and field on the right
				distance = measure(map[i][j], map[i][j + 1]);
				if (distance != -1) {
					addEdge(mapGraph, graphIndex(i, j), graphIndex(i, j + 1), distance);
				}

			}
			if (i != n - 1) {
				// edge between field and field under
				distance = measure(map[i][j], map[i + 1][j]);
				if (distance != -1) {
					addEdge(mapGraph, graphIndex(i, j), graphIndex(i + 1, j), distance);
				}
			}
		}
	}
}


// launch dijkstra algorithm from source to all 
int *dijkstra(GRAPH *graph, int source, int *tofind) {
	int i, j, k, vertices, *distances, x, y;
	char c;
	HEAP *heap;
	HEAPNODE *heapNode;
	NODE *node;

	// create minimal heap
	vertices = graph->vertices;
	distances = (int *)malloc(vertices * sizeof(int));

	heap = createHeap(vertices);

	// initialize rider for printing path
	graphPath = NULL;
	graphPath = (int *)malloc(vertices * sizeof(int));

	// fill minimal heap
	for (i = 0; i < vertices; i++) {
		distances[i] = INT_MAX;
		heap->nodes[i] = createHeapNode(i, distances[i]);
		heap->position[i] = i;

		// set rider to -1s
		graphPath[source] = -1;
	}

	// distance from source is 0
	heap->nodes[source] = createHeapNode(source, distances[source]);
	heap->position[source] = source;
	distances[source] = 0;
	decreaseKey(heap, source, distances[source]);

	heap->size = vertices;

	// find shortest distance for all nodes in minimal heap
	while (isHeapEmpty(heap) == 0) {

		// extract minimum
		heapNode = extractMinimum(heap);
		j = heapNode->vertex;

		// update distances for all nodes
		node = graph->list[j].head;
		while (node != NULL) {
			i = node->destination;

			if (isInHeap(heap, i) == 1 && distances[j] != INT_MAX && node->distance + distances[j] < distances[i]) {
				// shortest distance is not done & smaller than previous one
				
				//add step to path
				graphPath[i] = j;

				distances[i] = distances[j] + node->distance;

				decreaseKey(heap, i, distances[i]);
			}
			node = node->next;
		}

		// stop as soon as tofind empty
		c = 'X';
		x = mapIndexX(j);
		y = mapIndexY(j);

		if (x == dragon[0] && y == dragon[1]) {
			c = 'D';
			tofind[matrixIndex(c)] = 0;
		}
		else if (x == generator[0] && y == generator[1]) {
			c = 'G';
			tofind[matrixIndex(c)] = 0;
		}
		else if (x == START_X && y == START_Y) {
			c = 'S';
			tofind[matrixIndex(c)] = 0;
		}
		else {
			for (k = 0; k < princessCount; k++) {
				if (x == princesses[2 * k] && y == princesses[2 * k + 1]) {
					c = '1' + k;
					tofind[matrixIndex(c)] = 0;
					break;
				}
			}
		}

		if (c != 'X') {
			if (sumArray(tofind, TOTAL) == 0) {
				// return found distances from source
				return distances;
			}
		}
	}

	// non reachable
	return distances;
}

// save neccessary distances among special field to matrices
void determineDistances() {

	int *distance, i, j, *tofind;

	// dijkstra from dragon to generator, starting point, all princesses without teleports
	tofind = (int *)calloc(TOTAL, sizeof(int));
	tofind[matrixIndex('S')] = 1;
	if (generator[0] != -1) {
		tofind[matrixIndex('G')] = 1;
	}
	for (i = 0; i < princessCount; i++) {
		tofind[matrixIndex('1' + i)] = 1;
	}
	distance = dijkstra(mapGraph, graphIndex(dragon[0], dragon[1]), tofind);
	paths[2 * matrixIndex('D')] = graphPath;
	distBasic[matrixIndex('D')][matrixIndex('S')] = distBasic[matrixIndex('S')][matrixIndex('D')] = distance[graphIndex(START_X, START_Y)];
	if (generator[0] != -1) {
		distBasic[matrixIndex('D')][matrixIndex('G')] = distBasic[matrixIndex('G')][matrixIndex('D')] = distance[graphIndex(generator[0], generator[1])];
	}
	for (i = 0; i < princessCount; i++) {
		distBasic[matrixIndex('D')][matrixIndex('1' + i)] = distBasic[matrixIndex('1' + i)][matrixIndex('D')] = distance[graphIndex(princesses[2 * i], princesses[2 * i + 1])];
	}

	if (generator[0] != -1) {
		// dijkstra from generator to starting point, all princesses without teleports
		tofind = (int *)calloc(TOTAL, sizeof(int));
		tofind[matrixIndex('S')] = 1;
		for (i = 0; i < princessCount; i++) {
			tofind[matrixIndex('1' + i)] = 1;
		}
		distance = dijkstra(mapGraph, graphIndex(generator[0], generator[1]), tofind);
		paths[2 * matrixIndex('G')] = graphPath;
		distBasic[matrixIndex('G')][matrixIndex('S')] = distBasic[matrixIndex('S')][matrixIndex('G')] = distance[graphIndex(START_X, START_Y)];
		for (i = 0; i < princessCount; i++) {
			distBasic[matrixIndex('G')][matrixIndex('1' + i)] = distBasic[matrixIndex('1' + i)][matrixIndex('G')] = distance[graphIndex(princesses[2 * i], princesses[2 * i + 1])];
		}
	}

	for (i = 0; i < princessCount - 1; i++) {
		// dijkstra from princess to other, not yet determined princesses without teleports
		tofind = (int *)calloc(TOTAL, sizeof(int));
		for (j = i + 1; j < princessCount; j++) {
			tofind[matrixIndex('1' + j)] = 1;
		}
		distance = dijkstra(mapGraph, graphIndex(princesses[2 * i], princesses[2 * i + 1]), tofind);
		paths[2 * matrixIndex('1' + i)] = graphPath;
		for (j = i + 1; j < princessCount; j++) {
			distBasic[matrixIndex('1' + i)][matrixIndex('1' + j)] = distBasic[matrixIndex('1' + j)][matrixIndex('1' + i)] = distance[graphIndex(princesses[2 * j], princesses[2 * j + 1])];
		}
	}

	if (generator[0] != -1) {
		lauchTeleports();

		// dijkstra from dragon to generator, all princesses with teleports
		tofind = (int *)calloc(TOTAL, sizeof(int));
		tofind[matrixIndex('G')] = 1;
		for (i = 0; i < princessCount; i++) {
			tofind[matrixIndex('1' + i)] = 1;
		}
		distance = dijkstra(mapGraph, graphIndex(dragon[0], dragon[1]), tofind);
		paths[2 * matrixIndex('D') + 1] = graphPath;
		distGenerated[matrixIndex('D')][matrixIndex('G')] = distGenerated[matrixIndex('G')][matrixIndex('D')] = distance[graphIndex(generator[0], generator[1])];
		for (i = 0; i < princessCount; i++) {
			distGenerated[matrixIndex('D')][matrixIndex('1' + i)] = distGenerated[matrixIndex('1' + i)][matrixIndex('D')] = distance[graphIndex(princesses[2 * i], princesses[2 * i + 1])];
		}

		// dijkstra from generator to all princesses with teleports
		tofind = (int *)calloc(TOTAL, sizeof(int));
		for (i = 0; i < princessCount; i++) {
			tofind[matrixIndex('1' + i)] = 1;
		}
		distance = dijkstra(mapGraph, graphIndex(generator[0], generator[1]), tofind);
		paths[2 * matrixIndex('G') + 1] = graphPath;
		for (i = 0; i < princessCount; i++) {
			distGenerated[matrixIndex('G')][matrixIndex('1' + i)] = distGenerated[matrixIndex('1' + i)][matrixIndex('G')] = distance[graphIndex(princesses[2 * i], princesses[2 * i + 1])];
		}

		for (i = 0; i < princessCount - 1; i++) {
			// dijkstra from princess to other, not yet determined princesses with teleports
			tofind = (int *)calloc(TOTAL, sizeof(int));
			for (j = i + 1; j < princessCount; j++) {
				tofind[matrixIndex('1' + j)] = 1;
			}
			distance = dijkstra(mapGraph, graphIndex(princesses[2 * i], princesses[2 * i + 1]), tofind);
			paths[2 * matrixIndex('1' + i) + 1] = graphPath;
			for (j = i + 1; j < princessCount; j++) {
				distGenerated[matrixIndex('1' + i)][matrixIndex('1' + j)] = distGenerated[matrixIndex('1' + j)][matrixIndex('1' + i)] = distance[graphIndex(princesses[2 * j], princesses[2 * j + 1])];
			}
		}
	}
}


// build all possible string path variations
void permute(char *str, int left, int right) {
	int i, len, newLength;

	if (left == right) {
		// n + 2 variations from each of n!
		len = strlen(str);
		newLength = len + SPECIALS;
		vars[varsCount] = (char *)malloc((newLength + 1) * sizeof(char));
		vars[varsCount][0] = 'S';
		vars[varsCount][1] = 'G';
		vars[varsCount][2] = 'D';
		strncpy(vars[varsCount] + SPECIALS, str, len);
		vars[varsCount][newLength] = '\0';
		varsCount++;
		for (i = 1; i < newLength - 1; i++) {
			vars[varsCount] = (char *)malloc((newLength + 1) * sizeof(char));
			strcpy(vars[varsCount], vars[varsCount - 1]);
			swapChars(vars[varsCount] + i, vars[varsCount] + i + 1);
			varsCount++;
		}
	}
	else {
		for (i = left; i <= right; i++) {
			swapChars((str + left), (str + i));
			permute(str, left + 1, right);
			swapChars((str + left), (str + i));
		}
	}
}

// determine shortest path variaton
char *analyze() {

	int i, j, generated, sum, minsum, varsPrincess, varsTotal;
	char a, b, *best, *example;

	// (n + 2) * n!
	varsPrincess = factorial(princessCount);
	varsTotal = varsPrincess * (princessCount + 2);
	vars = (char **)malloc(varsTotal * sizeof(char *));

	// prepare sample variation string for princesses
	example = (char *)malloc((princessCount + 1) * sizeof(char));
	for (i = 0; i < princessCount; i++) {
		example[i] = '1' + i;
	}
	example[i] = '\0';
	// save variations
	varsCount = 0;
	permute(example, 0, princessCount - 1);

	minsum = INT_MAX;
	best = NULL;
	for (i = 0; i < varsTotal; i++) {
		sum = 0;
		generated = 0;
		for (j = 0; j < princessCount + SPECIALS - 1; j++) {
			a = vars[i][j];
			b = vars[i][j + 1];
			if (generator[0] == -1 && a == 'G') {
				// generator not within map
				sum = INT_MAX;
				break;
			}
			if (j == princessCount + SPECIALS - 2 && b == 'G') {
				// generator last, skip this subpath
				continue;
			}
			if (generated == 1) {
				sum += distGenerated[matrixIndex(a)][matrixIndex(b)];
			}
			else {
				sum += distBasic[matrixIndex(a)][matrixIndex(b)];
				if (b == 'G') {
					// switch to mode with teleports
					generated = 1;
				}
			}
		}
		if (sum < minsum) {
			minsum = sum;
			best = vars[i];
		}
	}

	/*****/
	//		t = minsum / 2 + starting-field-time
	/*****/

	// shortest time path
	return best;
}


// determine path from dijkstra saved paths
int getPath(char a, char b, int generated) {

	int matrixIndexA, matrixIndexB;

	// rider to be set
	graphPath = NULL;

	matrixIndexA = matrixIndex(a);
	matrixIndexB = matrixIndex(b);

	if (matrixIndexA < matrixIndexB) {
		graphPath = paths[2 * matrixIndexA + generated];
		// indicate browsing in standard order
		return 1;
	}
	else {
		graphPath = paths[2 * matrixIndexB + generated];
		// indicate browsing in reversed order
		return -1;
	}
}

// build final path
void go(char *sequence, int points) {

	int i, generated, x, y;
	char a, b;

	// join all subpaths
	generated = 0;
	for (i = 0; i < points - 1; i++) {
		a = sequence[i];
		b = sequence[i + 1];
		if (getPath(a, b, generated) > 0) {
			switch (b) {
			case 'G': {
				x = generator[0];
				y = generator[1];
				break;
			}
			default:
				x = princesses[2 * (b - '1')];
				y = princesses[2 * (b - '1') + 1];
				break;
			}
			addSubPath(graphIndex(x, y));
		}
		else {
			switch (a) {
			case 'S': {
				x = START_X;
				y = START_Y;
				break;
			}
			case 'G': {
				x = generator[0];
				y = generator[1];
				break;
			}
			default:
				x = princesses[2 * (a - '1')];
				y = princesses[2 * (a - '1') + 1];
				break;
			}
			addSubPathRev(graphIndex(x, y));
		}
		// remove last step of subpath, otherwise it would be doubled
		pathIndex -= 2;
		if (b == 'G') {
			generated = 1;
		}
	}
	// do not remove very last step
	pathIndex += 2;
}


// find path to dragon and then to all princesses
int *zachran_princezne(char **mapa, int n, int m, int t, int *dlzka_cesty) {

	char *sequence;
	int len;

	initPath();
	initTeleports();

	generator[0] = generator[1] = -1;
	loadMap(mapa, n , m);

	determineDistances();

	sequence = analyze();
	len = strlen(sequence);

	if (sequence[len - 1] == 'G') {
		// generator last (not within map or not neccessary)
		go(sequence, len - 1);
	}
	else {
		go(sequence, len);
	}

	*dlzka_cesty = pathIndex / 2;
	path = (int *)realloc(path, pathIndex * sizeof(int));
	return path;
}





int main() {

	char **mapa;
	int *cesta, n, m, t, dlzka_cesty;
	int i;

	t = 0;

	n = 5;
	m = 12;
	mapa = (char **)malloc(n * sizeof(char *));
	for (i = 0; i < n; i++) {
		mapa[i] = (char *)malloc(m * sizeof(char));
	}

	i = 0;
	for (i = 0; i < n; i++) {
		scanf("%s", mapa[i]);
	}

	cesta = zachran_princezne(mapa, n, m, t, &dlzka_cesty);

	for (i = 0; i < dlzka_cesty; ++i) {
		printf("%d %d\n", cesta[i * 2], cesta[i * 2 + 1]);
	}

	printf("%d\n", dlzka_cesty);

	return 0;
}

