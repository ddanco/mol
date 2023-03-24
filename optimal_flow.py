#!/usr/bin/env python3

from dataclasses import dataclass
from typing import Callable, Dict, FrozenSet, Optional, Tuple


Vertex = str
# Includes name to distinguish arcs with identical vertices
Arc = Tuple[Vertex, Vertex, str]
Tolls = Callable[[Arc], float]


@dataclass
class Graph:
  vertices: FrozenSet[Vertex]
  arcs: FrozenSet[Arc]


@dataclass
class Latencies:
  latencies: Dict[Arc, Callable[[float], float]]

  def __call__(self, arc: Arc) -> Callable[[float], float]:
    return self.latencies[arc]


@dataclass
class Commodity:
  pair: Tuple[Vertex, Vertex]
  demand: float


@dataclass
class SelfishRoutingInstance:
  graph: Graph
  latencies: Latencies
  commodities: Tuple[Commodity, ...]


@dataclass
class Flow:
  flow: Dict[Arc, Callable[[float], float]]

  def __call__(self, arc: Arc) -> Callable[[float], float]:
    return self.flow[arc]


def get_nash_flow(instance: SelfishRoutingInstance) -> Flow:
  # As this is not the focus of the problem, and we have
  # the solution already described in the lecture notes,
  # I am omitting this algorithm.
  ...


def get_optimal_flow(instance: SelfishRoutingInstance) -> Flow:
  # Same comment as get_nash_flow
  ...


def calculate_tolls_from_flows(
    instance: SelfishRoutingInstance,
    nash_flow: Flow,
    optimal_flow: Flow,
    sensitivity: float) -> Tolls:

  def get_commodity(arc: Arc) -> float:
    # This will only work for commodities between connected
    # vertices. For the sake of keeping this assignment somewhat
    # brief, I am leaving it this way, but for a proper solution,
    # should add graph functionality to check if arc is *on* any
    # path from commodity source to target, not just if they are
    # equal.
    for commodity in instance.commodities:
      if arc[:-1] == commodity.pair:
        return commodity.demand
    return 0.0

  def calculate_toll(arc: Arc) -> float:
    flow_on_nash = nash_flow(arc)(get_commodity(arc))
    flow_on_optimal = optimal_flow(arc)(get_commodity(arc))
    flow_difference = flow_on_nash - flow_on_optimal
    if flow_difference <= 0:
      return 0.0
    return flow_difference / sensitivity

  return lambda A: calculate_toll(A)


def get_tolls(instance: SelfishRoutingInstance, sensitivity: float) -> Tolls:
  return calculate_tolls_from_flows(
    instance,
    get_nash_flow(instance),
    get_optimal_flow(instance),
    sensitivity)


def print_tolls(instance: SelfishRoutingInstance, tolls: Tolls) -> None:
  print('Tolls per arc:\n')
  for arc in instance.graph.arcs:
    print(f'Arc: {arc}, Toll: {tolls(arc)}')


if __name__ == '__main__':

  # I know this all wasn't necessary. I just miss coding.

  pigou_graph = Graph(
    vertices=frozenset({'s', 't'}),
    arcs=frozenset({('s', 't', 'top'), ('s', 't', 'bottom')}))

  pigou_latencies = Latencies({
    ('s', 't', 'top'): lambda x: x,
    ('s', 't', 'bottom'): lambda x: 1.0})

  example_instance = SelfishRoutingInstance(
    pigou_graph,
    pigou_latencies,
    (Commodity(('s', 't'), 1),))

  example_optimal_flow = Flow({
    ('s', 't', 'top'): lambda x: 0.5*x,
    ('s', 't', 'bottom'): lambda x: 0.5*x})
  example_nash_flow = Flow({
    ('s', 't', 'top'): lambda x: x,
    ('s', 't', 'bottom'): lambda x: 0.0})
  example_sensitivity = 1

  # For this example, we provide the flows, but if
  # get_optimal_flow were implemented, we would call get_tolls
  print_tolls(
    example_instance,
    calculate_tolls_from_flows(
      example_instance,
      example_nash_flow,
      example_optimal_flow,
      example_sensitivity))

  ##################
  # Output when run:

  # Tolls per arc:

  # Arc: ('s', 't', 'top'), Toll: 0.5
  # Arc: ('s', 't', 'bottom'), Toll: 0.0

  ##################
