
.PHONY: build-docker
build-docker:
	$(MAKE) -f makefile gen
	docker build \
		-f ./build.Dockerfile \
		--target soap.coffee \
		-t www/soap.coffee:latest \
		.

static: build-docker
	docker create --name soap-coffee-build www/soap.coffee:latest
	docker cp soap-coffee-build:/bin/soap.coffee .
	docker rm -f soap-coffee-build
