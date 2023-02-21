#--------------------------------------------------------------------
# Author: Paul Brodersen, writer & maintainer of Netgraph library
#   (pip install netgraph)
# 
# This is an example of how to draw bounding sets around nodes
# in networkx graphs.
#--------------------------------------------------------------------

import numpy as np
import matplotlib.pyplot as plt
import networkx as nx

from itertools import combinations
from scipy.spatial.distance import cdist
from scipy.spatial.ckdtree import cKDTree
from scipy.ndimage import gaussian_filter
from matplotlib.path import Path
from matplotlib.patches import PathPatch

from netgraph import (
    Graph,
    get_sugiyama_layout,
    get_curved_edge_paths
)


if __name__ == '__main__':

    # fig, axes = plt.subplots(1, 3, sharex=True, sharey=True, figsize=(12, 4))
    fig, axes = plt.subplots(2, 2, sharex=True, sharey=True, figsize=(10, 10))
    axes = axes.ravel()

    n = 20
    g = nx.gnr_graph(n, 0.01)
    subset = np.random.choice(n, 5, replace=False)
    node_color = {node : 'red' if node in subset else 'blue' for node in g}
    node_positions = get_sugiyama_layout(list(g.edges)) # a.k.a 'dot'
    Graph(g, edge_width=0.5, node_layout=node_positions, node_color=node_color, arrows=True, ax=axes[0])

    # --------------------------------------------------------------------------------
    # Using the nodes in the subset, construct the minimum spanning tree using distance as the weight parameter.
    xy = np.array([node_positions[node] for node in subset])
    distances = cdist(xy, xy)
    h = nx.Graph()
    h.add_weighted_edges_from([(subset[ii], subset[jj], distances[ii, jj]) for ii, jj in combinations(range(len(subset)), 2)])
    h = nx.minimum_spanning_tree(h)

    Graph(g, edge_width=0.5, node_layout=node_positions, node_color=node_color, arrows=True, ax=axes[1])
    Graph(h, nodes=list(g.nodes), edge_width=3, edge_color='red', node_layout=node_positions, node_color=node_color, ax=axes[1])

    # --------------------------------------------------------------------------------
    # Compute an edge routing that avoids other nodes. Here I use
    # a modified version of the Fruchterman-Reingold algorithm to
    # place edge control points while avoiding the nodes.
    # Change the default origin and scale to make the canvas a bit
    # larger such that the curved edges can curve outside the bbox
    # covering the nodes.
    edge_paths = get_curved_edge_paths(list(h.edges), node_positions, k=0.25, origin=(-0.5, -0.5), scale=(2, 2))
    Graph(g, edge_width=0.5, node_layout=node_positions, node_color=node_color, arrows=True, ax=axes[2])
    for _, path in edge_paths.items():
        x, y = path.T
        axes[2].plot(x, y, color='magenta', linewidth=10, zorder=-1)

    # --------------------------------------------------------------------------------
    # Use nearest neighbour interpolation to partition the canvas into 2 regions.

    xy1 = np.concatenate(list(edge_paths.values()), axis=0)
    z1 = np.ones(len(xy1))

    xy2 = np.array([node_positions[node] for node in node_positions if node not in subset])
    z2 = np.zeros(len(xy2))

    # Add a frame around the axes.
    # This reduces the desired mask in regions where there are no nearby point from the exclusion list.
    xmin, xmax = axes[2].get_xlim()
    ymin, ymax = axes[2].get_ylim()
    xx = np.linspace(xmin, xmax, 100)
    yy = np.linspace(ymin, ymax, 100)

    left = np.c_[np.full_like(xx, xmin), yy]
    top = np.c_[xx, np.full_like(yy, ymax)]
    right = np.c_[np.full_like(xx, xmax), yy]
    bottom = np.c_[xx, np.full_like(yy, ymin)]

    xy3 = np.concatenate([left, top, right, bottom], axis=0)
    z3 = np.zeros((len(xy3)))

    xy = np.concatenate([xy1, xy2, xy3], axis=0)
    z = np.concatenate([z1, z2, z3])
    tree = cKDTree(xy)
    xy_grid = np.meshgrid(xx, yy)
    _, indices = tree.query(np.reshape(xy_grid, (2, -1)).T, k=1)
    z_grid = z[indices].reshape(xy_grid[0].shape)

    # smooth output
    z_smooth = gaussian_filter(z_grid, 1.5)

    Graph(g, edge_width=0.5, node_layout=node_positions, node_color=node_color, arrows=True, ax=axes[3])
    contour = axes[3].contour(xy_grid[0], xy_grid[1], z_smooth, np.array([0.9]), alpha=0)
    patch = PathPatch(contour.collections[0].get_paths()[0], facecolor='red', alpha=0.5, zorder=-1)
    axes[3].add_patch(patch)

    plt.show()