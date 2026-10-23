from adversary import controls,reached
import argparse
p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=4);p.add_argument('--limit',type=int,default=10);p.add_argument('--seed',type=int,default=614)
a=p.parse_args()
controls();reached(a.n,a.limit,a.seed)
