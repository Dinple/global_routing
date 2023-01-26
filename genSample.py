import os, sys
import re
import random
import numpy as np
import argparse
import subprocess
import networkx as nx
import matplotlib.pyplot as plt
import itertools
from util.util import *

""" Generating Sample Input Randomly for Global Routing Benchmark

Example:
    python3 genSample.py -vcnt [VERTEX_CNT]
"""
SEED = 15

def gen_pin_location(seed, vertex_count, scaling_factor):
    """_summary_

    Args:
        seed (_type_): _description_
        vertex_count (_type_): _description_
        scaling_factor (_type_): _description_
    """
    random.seed(seed)
    x_sample = random.sample(range(vertex_count * scaling_factor), vertex_count)
    y_sample = random.sample(range(vertex_count * scaling_factor), vertex_count)

    vertices = []
    # write to .gridLayout file
    with open('./gridLayout/{}_pin_seed_{}.gridLayout'.format(str(vertex_count), str(seed)), 'w+') as fp:
        fp.write("== Pin Locations ==" + "\n")
        for x, y in zip(x_sample, y_sample):
            vertices.append((x, y))
            fp.write(str(vertices[-1]) + "\n")
    return vertices

def extract_layout(layout_dir):
    for __, __, files in os.walk(layout_dir):
        for layout_file in files:
            if layout_file.endswith(".gridLayout"):
                with open(os.path.join(layout_dir, layout_file)) as file:
                    x_collection = []
                    y_collection = []
                    vert_collection = []
                    for line in file:
                        raw_pos = re.findall(r'\b\d+\b',line)
                        if raw_pos:
                            x_collection.append(int(raw_pos[0]))
                            y_collection.append(int(raw_pos[1]))
                            vert_collection.append((int(raw_pos[0]), int(raw_pos[1])))
                    return sorted(x_collection), sorted(y_collection), vert_collection

def gen_hanan_grid(x_collection, y_collection):
    return [[(x_collection[x], y_collection[y]) for x in range(len(x_collection))] for y in range(len(y_collection))] 

def gen_smt(seed, sample_dir, x_collection, y_collection, vert_collection):
    with open(os.path.join(sample_dir, '{}_pin_seed_{}.smt2')\
        .format(str(len(vert_collection)), str(seed)), 'w+') as fp:
        fp.write("; Begin SMT Formulation" + "\n" + "\n")

        fp.write("; Define Total Edges Cost\n")
        fp.write("(declare-const COST_Edge (_ BitVec 8))\n"+ "\n")

        fp.write("; Define Total Vertex Cost\n")
        fp.write("(declare-const COST_Vertex (_ BitVec 8))\n"+ "\n")

        fp.write("; Define Total Wirelength Cost\n")
        fp.write("(declare-const COST_WL (_ BitVec 8))\n"+ "\n")

        # Horizontal Edge Cost
        fp.write("; Define Horizontal Edge Cost\n")
        fp.write("(declare-const COST_H (_ BitVec 8))\n")
        fp.write("\n")

        # Vertical Edge Cost
        fp.write("; Define Vertical Edge Cost\n")
        fp.write("(declare-const COST_V (_ BitVec 8))\n")
        fp.write("\n")

        # Steiner Point Cost
        fp.write("; Define Steiner Point Cost\n")
        fp.write("(declare-const COST_sp (_ BitVec 8))\n")
        fp.write("(assert (= COST_sp (_ bv1 8)))\n")

        fp.write("\n")

        # Edge
        fp.write("; Define Edges\n")
        for x_idx in range(len(x_collection)):
            for y_idx in range(len(y_collection)):
                if not y_idx == len(y_collection) - 1:
                    # top
                    fp.write("(declare-const E_r{}c{}_r{}c{} Bool)\n".format(y_collection[y_idx], x_collection[x_idx],\
                                                                                y_collection[y_idx+1], x_collection[x_idx]))

                if not x_idx == len(x_collection) - 1:
                    # right
                    fp.write("(declare-const E_r{}c{}_r{}c{} Bool)\n".format(y_collection[y_idx], x_collection[x_idx],\
                                                                                y_collection[y_idx], x_collection[x_idx+1]))
    
        fp.write("\n")

        # Vertex
        fp.write("; Define Vertices (Driver, Sinks, Steiner)\n")
        for x_idx in range(len(x_collection)):
            for y_idx in range(len(y_collection)):
                fp.write("(declare-const V_r{}c{} Bool)\n".format(y_collection[y_idx], x_collection[x_idx]))

        fp.write("\n")

        fp.write("; Assert Driver and sinks vertices are used\n")
        for v_idx in range(len(vert_collection)):
            fp.write("(assert (= V_r{}c{} true))\n".format(vert_collection[v_idx][1], vert_collection[v_idx][0]))

        fp.write("\n")

        fp.write("; ; Assert if two vertices are used and share a common edge, the common edge should be used as well\n")
        for x_idx in range(len(x_collection)):
            for y_idx in range(len(y_collection)):
                fp.write("(assert (ite (= V_r{}c{} true) ((_ at-least 1) ".format(y_collection[y_idx], x_collection[x_idx]))
                # top
                if not y_idx == len(y_collection) - 1:
                    fp.write("E_r{}c{}_r{}c{} ".format(y_collection[y_idx], x_collection[x_idx],\
                                                        y_collection[y_idx+1], x_collection[x_idx]))
                
                # bottom (order of discovery)
                if not y_idx == 0:
                    fp.write("E_r{}c{}_r{}c{} ".format(y_collection[y_idx-1], x_collection[x_idx],\
                                                            y_collection[y_idx], x_collection[x_idx]))

                # right
                if not x_idx == len(x_collection) - 1:
                    fp.write("E_r{}c{}_r{}c{} ".format(y_collection[y_idx], x_collection[x_idx],\
                                                        y_collection[y_idx], x_collection[x_idx+1]))
                
                # left (order of discovery)
                if not x_idx == 0:
                    fp.write("E_r{}c{}_r{}c{} ".format(y_collection[y_idx], x_collection[x_idx-1],\
                                                        y_collection[y_idx], x_collection[x_idx]))  

                fp.write(") (= 1 1)))\n")
        
        fp.write("\n")

        fp.write("; Assert if an edge is used, the two immediate vertices is used as well\n")
        for x_idx in range(len(x_collection)):
            for y_idx in range(len(y_collection)):
                if not y_idx == len(y_collection) - 1:
                    # top
                    fp.write("(assert (ite (= E_r{}c{}_r{}c{} true) (and (= V_r{}c{} true) (= V_r{}c{} true)) (= 1 1)))\n"
                            .format(y_collection[y_idx], x_collection[x_idx], y_collection[y_idx+1], x_collection[x_idx],
                                y_collection[y_idx], x_collection[x_idx], y_collection[y_idx+1], x_collection[x_idx]))

                if not x_idx == len(x_collection) - 1:
                    # right
                    fp.write("(assert (ite (= E_r{}c{}_r{}c{} true) (and (= V_r{}c{} true) (= V_r{}c{} true)) (= 1 1)))\n"
                            .format(y_collection[y_idx], x_collection[x_idx],y_collection[y_idx], x_collection[x_idx+1],
                                y_collection[y_idx], x_collection[x_idx],y_collection[y_idx], x_collection[x_idx+1]))
    
        fp.write("\n")

        fp.write("; Assert if two vertices are used and share a common edge, the common edge should be used as well\n")
        for x_idx in range(len(x_collection)):
            for y_idx in range(len(y_collection)):
                if not y_idx == len(y_collection) - 1:
                    # top
                    fp.write("(assert (ite (and (= V_r{}c{} true) (= V_r{}c{} true)) (= E_r{}c{}_r{}c{} true) (= 1 1)))\n"
                            .format(y_collection[y_idx], x_collection[x_idx], y_collection[y_idx+1], x_collection[x_idx],
                                y_collection[y_idx], x_collection[x_idx], y_collection[y_idx+1], x_collection[x_idx]))

                if not x_idx == len(x_collection) - 1:
                    # right
                    fp.write("(assert (ite (and (= V_r{}c{} true) (= V_r{}c{} true)) (= E_r{}c{}_r{}c{} true) (= 1 1)))\n"
                            .format(y_collection[y_idx], x_collection[x_idx],y_collection[y_idx], x_collection[x_idx+1],
                                y_collection[y_idx], x_collection[x_idx],y_collection[y_idx], x_collection[x_idx+1]))

        fp.write("\n")

        fp.write("; Max steiner points is n - 1\n")
        fp.write("(assert ((_ at-most {}) ".format(len(vert_collection) - 1))
        for x_idx in range(len(x_collection)):
            for y_idx in range(len(y_collection)):
                if (x_collection[x_idx], y_collection[y_idx]) in vert_collection:
                    continue
                fp.write("V_r{}c{} ".format(y_collection[x_idx], x_collection[y_idx]))
        fp.write("))\n")

        fp.write("\n")

        fp.write(";; Horizontal wirelength\n")
        fp.write("(assert (= COST_H (bvadd ")
        for x_idx in range(len(x_collection)):
            for y_idx in range(len(y_collection)):
                if not x_idx == len(x_collection) - 1:
                    # top
                    fp.write("(ite ( = E_r{}c{}_r{}c{} true) (_ bv{} 8) (_ bv0 8))\n"
                        .format(y_collection[y_idx], x_collection[x_idx], 
                                y_collection[y_idx], x_collection[x_idx+1], 
                                (x_collection[x_idx+1] - x_collection[x_idx])))
        fp.write(")))\n")

        fp.write("\n")

        fp.write(";;; not equal to 0\n")
        fp.write("(assert (not (= COST_H (_ bv0 8))))\n")

        fp.write("\n")

        fp.write(";; Vertical wirelength\n")
        fp.write("(assert (= COST_V (bvadd ")
        for x_idx in range(len(x_collection)):
            for y_idx in range(len(y_collection)):
                if not y_idx == len(y_collection) - 1:
                    # right
                    fp.write("(ite ( = E_r{}c{}_r{}c{} true) (_ bv{} 8) (_ bv0 8))\n"
                        .format(y_collection[y_idx], x_collection[x_idx], 
                                y_collection[y_idx+1], x_collection[x_idx], 
                                (y_collection[y_idx+1] - y_collection[y_idx])))

        fp.write(")))\n")

        fp.write("\n")

        fp.write(";;; not equal to 0\n")
        fp.write("(assert (not (= COST_V (_ bv0 8))))\n")

        fp.write("\n")

        fp.write(";; ; Minimize total wirelength (shouldnt consider V/H separately)\n")
        fp.write("(assert (= COST_WL (bvadd COST_H COST_V)))\n")
        fp.write("(minimize COST_WL)\n")
        fp.write("\n")

        fp.write("; Minimize total edges used (no length considered, unit cost 1 per edge)\n")
        fp.write("(assert (= COST_Edge (bvadd \n")
        for x_idx in range(len(x_collection)):
            for y_idx in range(len(y_collection)):
                if not y_idx == len(y_collection) - 1:
                    # top
                    fp.write("(ite ( = E_r{}c{}_r{}c{} true) (_ bv1 8) (_ bv0 8))\n".format(y_collection[y_idx], x_collection[x_idx],\
                                                                                y_collection[y_idx+1], x_collection[x_idx]))

                if not x_idx == len(x_collection) - 1:
                    # right
                    fp.write("(ite ( = E_r{}c{}_r{}c{} true) (_ bv1 8) (_ bv0 8))\n".format(y_collection[y_idx], x_collection[x_idx],\
                                                                                y_collection[y_idx], x_collection[x_idx+1]))
        fp.write(")))\n")
        fp.write("(minimize COST_Edge)\n")
        fp.write("\n")

        
        fp.write("; Minimize total vertices used \n")
        fp.write("(assert (= COST_Vertex (bvadd \n")
        for x_idx in range(len(x_collection)):
            for y_idx in range(len(y_collection)):
                fp.write("(ite ( = V_r{}c{} true) (_ bv1 8) (_ bv0 8))\n".format(y_collection[y_idx], x_collection[x_idx]))
        fp.write(")))\n")
        fp.write("(minimize COST_Vertex)\n")
        fp.write("\n")

        fp.write("; Connectivity Property |E| = |V| - 1 \n")
        fp.write("(assert (= COST_Edge (bvsub  COST_Vertex (_ bv1 8))))\n")
        fp.write("\n")

        fp.write("(check-sat)\n")
        fp.write("(get-model)\n")
        fp.write("(get-objectives)\n")

    return str(os.path.join(sample_dir, '{}_pin_seed_{}.smt2')\
        .format(str(len(vert_collection)), str(seed)))

def z3_visual(res_path):
    G = nx.Graph()
    node_idx = 0
    node_bool_map = {}
    node_color_map = []

    with open(res_path) as file:
        for line1,line2 in itertools.zip_longest(*[file]*2):
            if re.findall(r'\(define-fun [V|E]',line1):
                raw_coord = re.findall(r'\d+',line1)
                raw_bool = re.findall(r'\w+',line2)
                if len(raw_coord) == 2:
                    # vertex
                    vname = "V_r{}c{}".format(int(raw_coord[0]), int(raw_coord[1]))
                    # print(vname)
                    G.add_node(vname, pos=(int(raw_coord[1]), int(raw_coord[0])))
                    # node_dict[(int(raw_coord[0]), int(raw_coord[1]))] = node_idx

                    # node_labels[node_idx]="V_r{}c{}".format(int(raw_coord[0]), int(raw_coord[1]))
                    # print(raw_bool)

                    node_bool_map[vname] = raw_bool[0]
                    if raw_bool[0] == "true":
                        node_color_map.append('red')
                    else:
                        node_color_map.append('blue')

                    node_idx += 1

    with open(res_path) as file:
        for line1,line2 in itertools.zip_longest(*[file]*2):
            if re.findall(r'\(define-fun [V|E]',line1):
                raw_coord = re.findall(r'\d+',line1)
                raw_bool = re.findall(r'\w+',line2)
                if len(raw_coord) == 4:
                    pass
                    # edge
                    vname1 = "V_r{}c{}".format(int(raw_coord[0]), int(raw_coord[1]))
                    vname2 = "V_r{}c{}".format(int(raw_coord[2]), int(raw_coord[3]))
                    
                    # edge_list.append(((int(raw_coord[0]), int(raw_coord[1])),
                    #                     (int(raw_coord[2]), int(raw_coord[3]))))
                    # edges.append([vname1, vname2])
                    # print(vname1, vname2, raw_bool[0])

                    # edge_bool_map.append(raw_bool[0])

                    # edge_bool_map[vname] = raw_bool[0]
                    if raw_bool[0] == "true":
                        G.add_edge(vname1, vname2, color='red')
                        # edge_color_map.append('red')
                    else:
                        G.add_edge(vname1, vname2, color='blue')
                        # edge_color_map.append('blue')

    print(nx.get_edge_attributes(G,'color'))
    
    nx.draw(G, node_color=node_color_map, 
                edge_color=nx.get_edge_attributes(G, 'color').values(),
                pos=nx.get_node_attributes(G,'pos'), 
                with_labels=True)
    plt.show()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('-vcnt', '--vertex_count', type=str, required=True)
    args = parser.parse_args()
    # generate at least 3 pin nets
    if int(args.vertex_count) < 3:
        print("[WARNING] Too few pin locations to generate.")
        exit(0)
    print("[INFO] Generating {} pin locations ...".format(args.vertex_count))
    gen_pin_location(seed=SEED, vertex_count=int(args.vertex_count)
                    , scaling_factor=4)

    # extract x/y location of the layout and get the hanan grid from x, y
    x_collection, y_collection, vert_collection = extract_layout("./gridLayout")

    G = nx.Graph()
    p = {}
    for vert in vert_collection:
        vname = "V_r{}c{}".format(int(vert[1]), int(vert[0]))
        G.add_node(vname)
        p[vname] = vert

    nx.draw(G, pos = p, with_labels = True)
    plt.show()

    # write to smt2 file
    smt_file = gen_smt(seed=SEED, sample_dir="Example", x_collection=x_collection,
                        y_collection=y_collection, vert_collection=vert_collection)
    
    subprocess.run(["z3", smt_file, ">", "out.z3"])

    os.system("z3 {} > ./Z3res/{}".format(smt_file, '{}_pin_seed_{}.z3'
        .format(str(len(vert_collection)), str(SEED))))

    z3_visual("./Z3res/{}".format('{}_pin_seed_{}.z3'.format(str(len(vert_collection)), str(SEED))))
    
if __name__ == "__main__":
    main()