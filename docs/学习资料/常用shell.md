# 常用Shell命令

## find 与grep一起使用

```
find . -type f -name "" -exec grep --color -nH --null -e "hello" \{\} +
```

## ubuntu安装go脚本

```

#!/bin/bash
apt update
apt install wget curl -y
bash
cd 

echo "1. install go"
cd ~ \
&& wget https://studygolang.com/dl/golang/go1.16.7.linux-amd64.tar.gz -O go16.7.linux-amd64.tar.gz \
&& tar -C ~/ -xzf go16.7.linux-amd64.tar.gz \
&& rm -f ~/go16.7.linux-amd64.tar.gz

echo "2. set env"
cd ~
mkdir ~/gopath
echo 'export GOPROXY=https://goproxy.io' >> ~/.bashrc
echo 'export GOPATH=~/gopath' >> ~/.bashrc
echo 'export PATH=$PATH:~/go/bin:$GOPATH/bin' >> ~/.bashrc
source ~/.bashrc

echo "3. check go app"
go version

echo "4. check go env"
go env

echo "5. create go source file"
cd ~
tee ./hello.go <<-'EOF'
package main

import "fmt"

func main() {
	fmt.Println("Hello world!")
}
EOF

echo "6. run hello.go"
go run hello.go

echo "go1.16 install and check finished"
```

