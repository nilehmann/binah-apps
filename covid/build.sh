#!/usr/bin/env bash

rm -rf dist
mkdir dist
cd client 
yarn build --dest ../dist/static

cd ../server
make build
stack install --local-bin-path ../dist
cp -r templates ../dist

